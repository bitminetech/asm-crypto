"""
Write the vector files for Keccak-256, HMAC-SHA-256, HKDF-SHA-256, AES-128
(CTR and GCM), secp256k1, ChaCha20-Poly1305, X25519 and P-256.

Usage: python3 -I primitives.py OUT_DIR
Environment: SECP256K1_LIBRARY, the libsecp256k1 shared library that
run.sh builds at the pinned commit.

Expected results:
- Keccak-256: the Keccak team's CompactFIPS202.py, at the pinned XKCP commit.
- HMAC, HKDF, AES, ChaCha20-Poly1305, X25519, P-256: the pinned
  `cryptography` package (OpenSSL); P-256 signatures with its RFC 6979 nonces.
- secp256k1: libsecp256k1 at the pinned commit, through its C interface.
- Official vectors (NIST, RFC, Wycheproof, devp2p) carry their own results. The
  script checks that the reference agrees with each one it uses.
The file format is in README.md.
"""

import base64
import ctypes
import hashlib
import io
import json
import os
import random
import re
import runpy
import struct
import sys
import urllib.request
import zipfile

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import hashes, hmac as chmac, poly1305
from cryptography.hazmat.primitives.asymmetric import ec, utils as ecutils, x25519
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM, ChaCha20Poly1305
from cryptography.hazmat.primitives.kdf.hkdf import HKDF, HKDFExpand

WYCHEPROOF = "https://raw.githubusercontent.com/C2SP/wycheproof/65ca494727a52944c204441c860b039e6786b99b/testvectors_v1/"
DEVP2P = "https://raw.githubusercontent.com/ethereum/devp2p/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/"
NIST = "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/"
RFC = "https://www.rfc-editor.org/rfc/"
SOURCES = {
    "CompactFIPS202.py": ("https://raw.githubusercontent.com/XKCP/XKCP/d20c8fcaecc543f816a0721d0dfc13b4cf27c14d/Standalone/CompactFIPS202/Python/CompactFIPS202.py",
                          "0b731097a4dfcf33fdaf395ac0bee81c6a6ebff2975590c35ad8cd8d6f3c204f"),
    "hmac_sha256_test.json": (WYCHEPROOF + "hmac_sha256_test.json", "2d201cfa61d1bf95e6f5d07d96634b4a348b31e8eaa277ad7c8d09677b7a743f"),
    "hkdf_sha256_test.json": (WYCHEPROOF + "hkdf_sha256_test.json", "bb2b462a38b251cb52a2aede706d6d4b62b26864f4e80c95497507ddb07c5f1e"),
    "aes_gcm_test.json": (WYCHEPROOF + "aes_gcm_test.json", "985e5ecc172e181eaf49e89508b9470dcf478002eb7e8559c707eb42dc97dfe7"),
    "ecdsa_secp256k1_sha256_p1363_test.json": (WYCHEPROOF + "ecdsa_secp256k1_sha256_p1363_test.json",
                                               "7a339efc7134fb2495cd32afdbd692e0f86427d3c24e9073f6a7d858bb8788d2"),
    "ecdh_secp256k1_test.json": (WYCHEPROOF + "ecdh_secp256k1_test.json", "049fa2be70e9db836a043aba6132b53cd97de4c0de5277bca6d65a2770075cae"),
    "discv5-wire-test-vectors.md": (DEVP2P + "discv5/discv5-wire-test-vectors.md", "dbcb81f70bc963cad2d5b28fd7ef99e0c4b4ce4d03497f7c75d63ef752115170"),
    "enr.md": (DEVP2P + "enr.md", "29260bceb96e289140dc08c1336e1f26e070613664a7ec6db72fffbfb85cc58d"),
    "KAT_AES.zip": (NIST + "aes/KAT_AES.zip", "a203b16c9246b2ebae31dee5de21a606be80cf78ceabaca37150236fa098eb60"),
    "gcmtestvectors.zip": (NIST + "mac/gcmtestvectors.zip", "f9fc479e134cde2980b3bb7cddbcb567b2cd96fd753835243ed067699f26a023"),
    "chacha20_poly1305_test.json": (WYCHEPROOF + "chacha20_poly1305_test.json", "fe61d25f90e1bde4461d00eafe61049e5f29bd999f36b766df9cda90906ad53d"),
    "x25519_test.json": (WYCHEPROOF + "x25519_test.json", "35c3f5231cf25cc640b524d403461deee9e49441d5d915a3a25b2c8ff5adbe7d"),
    "ecdsa_secp256r1_sha256_p1363_test.json": (WYCHEPROOF + "ecdsa_secp256r1_sha256_p1363_test.json",
                                               "c60de693930e386c3a5472d08081623ef8504decc54b38ac01ec6b2a2575c986"),
    "rfc7748.txt": (RFC + "rfc7748.txt", "279ca0ecc5e92e2962e27b846986aeb74729d9dd34bd4a04a362f80dcb596ad3"),
    "rfc8439.txt": (RFC + "rfc8439.txt", "25bef70fbf7a07ff45c2fe4cb7c6ce954eac687413d8610603268b4e4415324c"),
    "rfc6979.txt": (RFC + "rfc6979.txt", "456e8f17558fdbd206f968b96fc6f1b4a71ea331ab30ad17f711ab3adaa7d701"),
    "186-4ecdsatestvectors.zip": (NIST + "dss/186-4ecdsatestvectors.zip", "fe47cc92b4cee418236125c9ffbcd9bb01c8c34e74a4ba195d954bcb72824752"),
}

# include/crypto.inc, include/hmac.inc, include/aes.inc, include/chacha20.inc and include/x25519.inc
OK, HKDF_LENGTH, GCM_FAIL, INVALID_PRIVATE_KEY, INVALID_PUBLIC_KEY = 0, 2, 3, 4, 5
CHACHA_FAIL, X25519_ZERO = 6, 7

KIND_KECCAK, KIND_HMAC, KIND_HKDF, KIND_CTR, KIND_GCM = 1, 2, 3, 4, 5
KIND_PUBLIC_KEY, KIND_DECOMPRESS, KIND_ECDH, KIND_SIGN, KIND_VERIFY = 6, 7, 8, 9, 10
KIND_CHACHA, KIND_X25519, KIND_P256_PUBLIC_KEY, KIND_P256_SIGN, KIND_P256_VERIFY = 11, 12, 13, 14, 15
KIND_POLY1305 = 16

# P-256 (FIPS 186-5 / SP 800-186): the field prime and the group order.
P256_P = 2**256 - 2**224 + 2**192 + 2**96 - 1
P256_N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F


def fail(text):
    sys.exit("primitives.py: " + text)


def fetch(out, name):
    url, sha = SOURCES[name]
    path = os.path.join(out, "sources", name)
    if os.path.exists(path):
        with open(path, "rb") as f:
            data = f.read()
        if hashlib.sha256(data).hexdigest() == sha:
            return data
    request = urllib.request.Request(url, headers={"User-Agent": "asm-crypto-vector-generator"})
    with urllib.request.urlopen(request) as r:
        data = r.read()
    if hashlib.sha256(data).hexdigest() != sha:
        fail(f"{name}: SHA-256 {hashlib.sha256(data).hexdigest()}, pinned {sha}")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "wb") as f:
        f.write(data)
    return data


def u64(v):
    return struct.pack("<Q", v)


def blob(b):
    return u64(len(b)) + bytes(b)


class VectorFile:
    def __init__(self):
        self.cases, self.seen = [], set()

    def add(self, kind, name, body):
        key = hashlib.sha256(u64(kind) + body).digest()
        if key in self.seen:
            return
        self.seen.add(key)
        self.cases.append(u64(kind) + blob(name.encode()) + body)

    def write(self, path):
        with open(path, "wb") as f:
            f.write(b"CRYPTOV2" + u64(len(self.cases)))
            for c in self.cases:
                f.write(c)


# ---------------------------------------------------------------- References


class Secp256k1:
    """libsecp256k1 through its C interface."""

    COMPRESSED, UNCOMPRESSED = 258, 2

    def __init__(self, path):
        lib = self.lib = ctypes.CDLL(path)
        lib.secp256k1_context_create.restype = ctypes.c_void_p
        lib.secp256k1_context_create.argtypes = [ctypes.c_uint]
        for name in ("secp256k1_ec_seckey_verify", "secp256k1_ec_pubkey_create", "secp256k1_ec_pubkey_serialize",
                     "secp256k1_ec_pubkey_parse", "secp256k1_ecdsa_sign", "secp256k1_ecdsa_signature_serialize_compact",
                     "secp256k1_ecdsa_signature_parse_compact", "secp256k1_ecdsa_verify", "secp256k1_ecdh"):
            getattr(lib, name).argtypes = None
        self.ctx = ctypes.c_void_p(lib.secp256k1_context_create(1))
        self.hashfp = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p)(
            self._compressed)

    @staticmethod
    def _compressed(output, x32, y32, data):
        y = ctypes.string_at(y32, 32)
        ctypes.memmove(output, bytes([2 | (y[31] & 1)]) + ctypes.string_at(x32, 32), 33)
        return 1

    def _parse(self, pub):
        point = ctypes.create_string_buffer(64)
        ok = self.lib.secp256k1_ec_pubkey_parse(self.ctx, point, pub, ctypes.c_size_t(len(pub)))
        return point if ok == 1 else None

    def _serialize(self, point, flags):
        out = ctypes.create_string_buffer(65)
        size = ctypes.c_size_t(65)
        self.lib.secp256k1_ec_pubkey_serialize(self.ctx, out, ctypes.byref(size), point, ctypes.c_uint(flags))
        return out.raw[: size.value]

    def public_key(self, priv):
        point = ctypes.create_string_buffer(64)
        if self.lib.secp256k1_ec_pubkey_create(self.ctx, point, priv) != 1:
            return None
        return self._serialize(point, self.COMPRESSED)

    def decompress(self, pub):
        """The 64 bytes x || y of a 33-byte compressed key, or None."""
        if len(pub) != 33 or pub[0] not in (2, 3):
            return None
        point = self._parse(pub)
        return None if point is None else self._serialize(point, self.UNCOMPRESSED)[1:]

    def ecdh(self, pub, priv):
        if len(pub) != 33 or pub[0] not in (2, 3):
            return INVALID_PUBLIC_KEY, None
        point = self._parse(pub)
        if point is None:
            return INVALID_PUBLIC_KEY, None
        if self.lib.secp256k1_ec_seckey_verify(self.ctx, priv) != 1:
            return INVALID_PRIVATE_KEY, None
        out = ctypes.create_string_buffer(33)
        if self.lib.secp256k1_ecdh(self.ctx, out, point, priv, self.hashfp, None) != 1:
            fail("libsecp256k1 ECDH failed for valid inputs")
        return OK, out.raw

    def sign(self, priv, msg32):
        sig = ctypes.create_string_buffer(64)
        if self.lib.secp256k1_ecdsa_sign(self.ctx, sig, msg32, priv, None, None) != 1:
            return INVALID_PRIVATE_KEY, None
        out = ctypes.create_string_buffer(64)
        self.lib.secp256k1_ecdsa_signature_serialize_compact(self.ctx, out, sig)
        return OK, out.raw

    def verify(self, pub, msg32, sig64):
        """(status, valid) as crypto_secp256k1_verify gives them."""
        if len(pub) != 33 or pub[0] not in (2, 3):
            return INVALID_PUBLIC_KEY, 0
        point = self._parse(pub)
        if point is None:
            return INVALID_PUBLIC_KEY, 0
        sig = ctypes.create_string_buffer(64)
        if self.lib.secp256k1_ecdsa_signature_parse_compact(self.ctx, sig, sig64) != 1:
            return OK, 0
        return OK, int(self.lib.secp256k1_ecdsa_verify(self.ctx, sig, msg32, point) == 1)


def hmac_sha256(key, msg):
    h = chmac.HMAC(key, hashes.SHA256())
    h.update(msg)
    return h.finalize()


def hkdf_expand(prk, info, length):
    return HKDFExpand(hashes.SHA256(), length, info).derive(prk)


def aes_ctr(key, counter, data):
    e = Cipher(algorithms.AES(key), modes.CTR(counter)).encryptor()
    return e.update(data) + e.finalize()


# ---------------------------------------------------------------- Cases


def keccak_case(f, keccak, name, msg, want=None):
    digest = bytes(keccak(1088, 512, bytearray(msg), 0x01, 32))
    if want is not None and digest != want:
        fail(f"{name}: the Keccak reference does not give the official digest")
    f.add(KIND_KECCAK, name, blob(msg) + digest)


def hmac_case(f, name, key, msg, want_prefix=None):
    mac = hmac_sha256(key, msg)
    if want_prefix is not None and mac[: len(want_prefix)] != want_prefix:
        fail(f"{name}: cryptography does not give the official HMAC")
    f.add(KIND_HMAC, name, blob(key) + blob(msg) + mac)


def hkdf_case(f, name, salt, ikm, info, length, want=None):
    prk = hmac_sha256(salt, ikm)
    if length > 255 * 32:
        status, okm = HKDF_LENGTH, b""
    else:
        status, okm = OK, hkdf_expand(prk, info, length)
        if okm != HKDF(hashes.SHA256(), length, salt, info).derive(ikm):
            fail(f"{name}: HKDF and Extract with Expand differ")
    if want is not None and okm != want:
        fail(f"{name}: cryptography does not give the official HKDF output")
    f.add(KIND_HKDF, name, blob(salt) + blob(ikm) + blob(info) + u64(length) + u64(status) + prk + blob(okm))


def ctr_case(f, name, key, counter, data, want=None):
    out = aes_ctr(key, counter, data)
    if want is not None and out != want:
        fail(f"{name}: cryptography does not give the official CTR output")
    f.add(KIND_CTR, name, key + counter + blob(data) + blob(out))


def gcm_case(f, name, key, iv, pt, aad, sealed=None, valid=True):
    """A GCM case. With valid False, sealed is a tampered input that must fail."""
    if valid:
        got = AESGCM(key).encrypt(iv, pt, aad)
        if sealed is not None and got != sealed:
            fail(f"{name}: cryptography does not give the official GCM output")
        sealed = got
    else:
        try:
            AESGCM(key).decrypt(iv, sealed, aad)
            fail(f"{name}: cryptography accepts a case marked invalid")
        except Exception as e:
            if type(e).__name__ != "InvalidTag":
                raise
        pt = b""
    f.add(KIND_GCM, name, key + iv + blob(aad) + blob(pt) + blob(sealed) + u64(OK if valid else GCM_FAIL))


def pub_case(f, ref, name, priv):
    pub = ref.public_key(priv)
    f.add(KIND_PUBLIC_KEY, name, priv + u64(OK if pub else INVALID_PRIVATE_KEY) + (pub or bytes(33)))


def decompress_case(f, ref, name, pub):
    point = ref.decompress(pub)
    f.add(KIND_DECOMPRESS, name, pub + u64(OK if point else INVALID_PUBLIC_KEY) + (point or bytes(64)))


def ecdh_case(f, ref, name, pub, priv, want=None):
    status, shared = ref.ecdh(pub, priv)
    if want is not None and shared != want:
        fail(f"{name}: libsecp256k1 does not give the official shared secret")
    f.add(KIND_ECDH, name, pub + priv + u64(status) + (shared or bytes(33)))


def sign_case(f, ref, name, priv, msg, want=None):
    status, sig = ref.sign(priv, msg)
    if want is not None and sig != want:
        fail(f"{name}: libsecp256k1 does not give the official signature")
    f.add(KIND_SIGN, name, priv + msg + u64(status) + (sig or bytes(64)))
    return sig


def verify_case(f, ref, name, pub, msg, sig, want=None):
    status, valid = ref.verify(pub, msg, sig)
    if want is not None and (status, valid) != want:
        fail(f"{name}: libsecp256k1 gives {(status, valid)}, the official result is {want}")
    f.add(KIND_VERIFY, name, pub + msg + sig + u64(status) + u64(valid))


def chacha_case(f, name, key, nonce, pt, aad, sealed=None, valid=True):
    """A ChaCha20-Poly1305 case. With valid False, sealed is a tampered input that must fail."""
    if valid:
        got = ChaCha20Poly1305(key).encrypt(nonce, pt, aad)
        if sealed is not None and got != sealed:
            fail(f"{name}: cryptography does not give the official ChaCha20-Poly1305 output")
        sealed = got
    else:
        try:
            ChaCha20Poly1305(key).decrypt(nonce, sealed, aad)
            fail(f"{name}: cryptography accepts a case marked invalid")
        except Exception as e:
            if type(e).__name__ != "InvalidTag":
                raise
        pt = b""
    f.add(KIND_CHACHA, name, key + nonce + blob(aad) + blob(pt) + blob(sealed) + u64(OK if valid else CHACHA_FAIL))


def poly1305_case(f, name, key, msg, want=None):
    tag = poly1305.Poly1305.generate_tag(key, msg)
    if want is not None and tag != want:
        fail(f"{name}: cryptography does not give the official Poly1305 tag")
    f.add(KIND_POLY1305, name, key + blob(msg) + tag)


def x25519_ref(scalar, u):
    """(status, result) as crypto_x25519 gives them: X25519_ZERO for an all-zero result."""
    try:
        out = x25519.X25519PrivateKey.from_private_bytes(scalar).exchange(x25519.X25519PublicKey.from_public_bytes(u))
    except ValueError:
        return X25519_ZERO, None
    if out == bytes(32):
        return X25519_ZERO, None
    return OK, out


def x25519_case(f, name, scalar, u, want=None):
    status, out = x25519_ref(scalar, u)
    if want is not None and (status, out) != want:
        fail(f"{name}: cryptography gives {(status, out)}, the official result is {want}")
    f.add(KIND_X25519, name, scalar + u + u64(status) + (out or bytes(32)))
    return out


class P256:
    """P-256 through the pinned cryptography package."""

    CURVE = ec.SECP256R1()

    @staticmethod
    def private(priv):
        d = int.from_bytes(priv, "big")
        return ec.derive_private_key(d, P256.CURVE) if 0 < d < P256_N else None

    @staticmethod
    def public_key(priv):
        k = P256.private(priv)
        if k is None:
            return None
        nums = k.public_key().public_numbers()
        return b"\x04" + nums.x.to_bytes(32, "big") + nums.y.to_bytes(32, "big")

    @staticmethod
    def load(pub):
        """The public key object of a 65-byte uncompressed point, or None."""
        if len(pub) != 65 or pub[0] != 4:
            return None
        try:
            return ec.EllipticCurvePublicKey.from_encoded_point(P256.CURVE, pub)
        except ValueError:
            return None

    @staticmethod
    def sign(priv, hash32):
        k = P256.private(priv)
        if k is None:
            return INVALID_PRIVATE_KEY, None
        der = k.sign(hash32, ec.ECDSA(ecutils.Prehashed(hashes.SHA256()), deterministic_signing=True))
        r, s = ecutils.decode_dss_signature(der)
        return OK, r.to_bytes(32, "big") + s.to_bytes(32, "big")

    @staticmethod
    def verify(pub, hash32, sig64):
        key = P256.load(pub)
        if key is None:
            return INVALID_PUBLIC_KEY, 0
        r, s = int.from_bytes(sig64[:32], "big"), int.from_bytes(sig64[32:], "big")
        if not (0 < r < P256_N and 0 < s < P256_N):
            return OK, 0
        try:
            key.verify(ecutils.encode_dss_signature(r, s), hash32, ec.ECDSA(ecutils.Prehashed(hashes.SHA256())))
            return OK, 1
        except InvalidSignature:
            return OK, 0


def p256_pub_case(f, name, priv, want=None):
    pub = P256.public_key(priv)
    if want is not None and pub != want:
        fail(f"{name}: cryptography does not give the official public key")
    f.add(KIND_P256_PUBLIC_KEY, name, priv + u64(OK if pub else INVALID_PRIVATE_KEY) + (pub or bytes(65)))
    return pub


def p256_sign_case(f, name, priv, hash32, want=None):
    status, sig = P256.sign(priv, hash32)
    if want is not None and sig != want:
        fail(f"{name}: cryptography does not give the official signature")
    f.add(KIND_P256_SIGN, name, priv + hash32 + u64(status) + (sig or bytes(64)))
    return sig


def p256_verify_case(f, name, pub, hash32, sig64, want=None):
    status, valid = P256.verify(pub, hash32, sig64)
    if want is not None and (status, valid) != want:
        fail(f"{name}: cryptography gives {(status, valid)}, the official result is {want}")
    f.add(KIND_P256_VERIFY, name, pub + hash32 + sig64 + u64(status) + u64(valid))


# ---------------------------------------------------------------- Official vectors


def rsp_sections(text):
    """Records of a NIST .rsp file, each a dict, with its [section] values."""
    out, section, record = [], {}, {}
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("["):
            if record:
                out.append(record)
                record = {}
            m = re.match(r"\[(\w+)(?: = (\w+))?\]", line)
            if m:
                if m.group(2) is None:
                    section = {"mode": m.group(1)}
                else:
                    section[m.group(1)] = m.group(2)
        elif "=" in line:
            k, v = [s.strip() for s in line.split("=", 1)]
            if k.lower() == "count" and record:
                out.append(record)
                record = {}
            record[k] = v
            record.update({"_" + a: b for a, b in section.items()})
        elif line == "FAIL":
            record["FAIL"] = True
    if record:
        out.append(record)
    return out


def hexb(text):
    text = text.strip()
    return bytes.fromhex(text[2:] if text.startswith("0x") else text)


def md_values(text):
    """name = 0x... or name: 0x... pairs of the devp2p test vector document."""
    return {m.group(1): m.group(2) for m in re.finditer(r"^\s+([\w-]+)\s*[:=]\s*(0x[0-9a-fA-F]*)\s*$", text, re.M)}


def rlp_decode_list(data):
    """The items of an RLP list of byte strings (enough for an ENR)."""
    def item(b, i):
        p = b[i]
        if p < 0x80:
            return b[i : i + 1], i + 1
        if p <= 0xB7:
            n = p - 0x80
            return b[i + 1 : i + 1 + n], i + 1 + n
        if p <= 0xBF:
            ln = p - 0xB7
            n = int.from_bytes(b[i + 1 : i + 1 + ln], "big")
            return b[i + 1 + ln : i + 1 + ln + n], i + 1 + ln + n
        fail("unexpected nested list in an ENR")
    p = data[0]
    if 0xC0 <= p <= 0xF7:
        i, end = 1, 1 + p - 0xC0
    else:
        ln = p - 0xF7
        i, end = 1 + ln, 1 + ln + int.from_bytes(data[1 : 1 + ln], "big")
    items = []
    while i < end:
        v, i = item(data, i)
        items.append(v)
    return items


def rlp_encode_list(items):
    def bytes_(b):
        if len(b) == 1 and b[0] < 0x80:
            return b
        if len(b) < 56:
            return bytes([0x80 + len(b)]) + b
        n = len(b).to_bytes((len(b).bit_length() + 7) // 8, "big")
        return bytes([0xB7 + len(n)]) + n + b
    payload = b"".join(bytes_(i) for i in items)
    if len(payload) < 56:
        return bytes([0xC0 + len(payload)]) + payload
    n = len(payload).to_bytes((len(payload).bit_length() + 7) // 8, "big")
    return bytes([0xF7 + len(n)]) + n + payload


def rfc_section(text, start, end):
    """The text from the line that starts with start to the line that starts with end."""
    a = re.search(r"^" + re.escape(start), text, re.M)
    b = re.search(r"^" + re.escape(end), text[a.end():], re.M)
    return text[a.start(): a.end() + b.start()]


def rfc_dump(section, label):
    """The bytes of the hex dump after the line with label, in RFC 8439 form:
    "NNN  hh hh ...  ascii" rows or "hh:hh:..." rows, across page breaks."""
    lines = section.splitlines()
    i = next(k for k, line in enumerate(lines) if line.strip() == label)
    out = bytearray()
    for line in lines[i + 1:]:
        t = line.strip()
        if not t or t.startswith("Nir & Langley") or t.startswith("RFC 8439"):
            continue
        m = re.match(r"^\d{3}\s+(.*)$", t)
        if m:
            hexpart = re.split(r"\s{2,}", m.group(1))[0]
            out += bytes(int(h, 16) for h in hexpart.split())
            continue
        if re.fullmatch(r"(?:[0-9a-f]{2}:)+(?:[0-9a-f]{2})?:?", t):
            out += bytes(int(h, 16) for h in t.strip(":").split(":"))
            continue
        if re.fullmatch(r"(?:[0-9A-Fa-f]{2} )*[0-9A-Fa-f]{2}", t):
            out += bytes.fromhex(t)
            continue
        break
    if not out:
        fail(f"rfc 8439: no bytes after {label!r}")
    return bytes(out)


def p256_sqrt(v):
    """A square root mod p of v, or None (p = 3 mod 4)."""
    r = pow(v, (P256_P + 1) // 4, P256_P)
    return r if r * r % P256_P == v % P256_P else None


def p256_x_of_y(y):
    """An x with x^3 - 3x + b = y^2 mod p, or None: the roots of the cubic, by gcd with x^p - x and splitting."""
    p = P256_P
    b = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
    f = [(b - y * y) % p, p - 3, 0, 1]                  # coefficients, low first, monic

    def trim(a):
        while a and a[-1] == 0:
            a.pop()
        return a

    def mod(a, m):
        a = trim(list(a))
        while len(a) >= len(m):
            c, s = a[-1] * pow(m[-1], -1, p) % p, len(a) - len(m)
            for i, v in enumerate(m):
                a[s + i] = (a[s + i] - c * v) % p
            a = trim(a)
        return a

    def mulmod(a, c, m):
        out = [0] * (len(a) + len(c))
        for i, u in enumerate(a):
            for j, v in enumerate(c):
                out[i + j] = (out[i + j] + u * v) % p
        return mod(out, m)

    def powmod(a, e, m):
        r, a = [1], mod(a, m)
        while e:
            if e & 1:
                r = mulmod(r, a, m)
            a, e = mulmod(a, a, m), e >> 1
        return r

    def gcd(a, c):
        a, c = trim(list(a)), trim(list(c))
        while c:
            a, c = c, mod(a, c)
        return a

    xp = powmod([0, 1], p, f) + [0] * 3                  # x^p mod f, then x^p - x
    xp[1] = (xp[1] - 1) % p
    g = gcd(f, xp)
    rng_ = random.Random(y)
    while len(g) > 2:
        a = rng_.randrange(p)
        h = powmod([a, 1], (p - 1) // 2, g)
        h = (h + [0] * len(g))[: len(g)]
        h[0] = (h[0] - 1) % p
        d = gcd(g, h)
        if 1 < len(d) < len(g):
            g = d
    if len(g) != 2:
        return None
    return (-g[0]) * pow(g[1], -1, p) % p


def rfc7748_x25519(text):
    """(scalar, u, result) of the two X25519 vectors and the iteration results of RFC 7748 section 5.2."""
    sec = rfc_section(text, "5.2.  Test Vectors", "6.  Diffie-Hellman")
    x25519_part = sec.split("X448:")[0]
    singles = re.findall(r"Input scalar:\s+([0-9a-f]{64}).*?Input u-coordinate:\s+([0-9a-f]{64}).*?"
                         r"Output u-coordinate:\s+([0-9a-f]{64})", x25519_part, re.S)
    iteration_part = sec[sec.index("For each iteration"):].split("X448:")[0]
    iters = re.findall(r"After (one|[\d,]+) iterations?:\s+([0-9a-f]{64})", iteration_part)
    iters = [("1" if k == "one" else k, v) for k, v in iters]
    dh = rfc_section(text, "6.1.  Curve25519", "6.2.  Curve448")
    keys = dict(re.findall(r"(Alice's private key, a|Alice's public key, X25519\(a, 9\)|Bob's private key, b|"
                           r"Bob's public key, X25519\(b, 9\)|Their shared secret, K):\s+([0-9a-f]{64})", dh))
    return [tuple(bytes.fromhex(v) for v in t) for t in singles], [(int(k.replace(",", "")), bytes.fromhex(v)) for k, v in iters], \
        {k: bytes.fromhex(v) for k, v in keys.items()}


def rfc6979_p256(text):
    """The P-256 key and the SHA-256 signatures of RFC 6979 section A.2.5."""
    sec = rfc_section(text, "A.2.5.  ECDSA, 256 Bits (Prime Field)", "A.2.6.  ECDSA, 384 Bits (Prime Field)")
    flat = re.sub(r"\s+", " ", sec)
    x = int(re.search(r"private key: x = ([0-9A-F]+) ", flat).group(1), 16)
    ux = int(re.search(r"Ux = ([0-9A-F]+) ", flat).group(1), 16)
    uy = int(re.search(r"Uy = ([0-9A-F]+) ", flat).group(1), 16)
    sigs = []
    for msg in ("sample", "test"):
        m = re.search(r'With SHA-256, message = "' + msg + r'": k = [0-9A-F]+ r = ([0-9A-F]+) s = ([0-9A-F]+) ', flat)
        r, s = (int(g, 16) for g in m.groups())
        sigs.append((msg.encode(), r.to_bytes(32, "big") + s.to_bytes(32, "big")))
    return x.to_bytes(32, "big"), b"\x04" + ux.to_bytes(32, "big") + uy.to_bytes(32, "big"), sigs


def cavp_ecdsa(text):
    """Records of a 186-4 ECDSA .rsp file, each a dict with the [curve,hash] section under "_section"."""
    out, section, record = [], "", {}
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("["):
            if re.fullmatch(r"\[[PKB]-\d+(,SHA-\d+)?\]", line):
                section = line.strip("[]")
            continue
        if " = " not in line:
            if record:
                out.append(record)
                record = {}
            continue
        k, v = line.split(" = ", 1)
        if k in record:
            out.append(record)
            record = {}
        record[k] = v
        record["_section"] = section
    if record:
        out.append(record)
    return out


def cavp_point(r):
    """The 65-byte uncompressed point of a CAVP record, or None when x or y needs more than 32 bytes."""
    x, y = int(r["Qx"], 16), int(r["Qy"], 16)
    if x >> 256 or y >> 256:
        return None
    return b"\x04" + x.to_bytes(32, "big") + y.to_bytes(32, "big")


# ---------------------------------------------------------------- Main


def main(out):
    rng = random.Random(778)
    ref = Secp256k1(os.environ["SECP256K1_LIBRARY"])
    keccak = runpy.run_path(os.path.join(out, "sources", "CompactFIPS202.py") if fetch(out, "CompactFIPS202.py") else "")["Keccak"]
    files = {}

    def f(name):
        return files.setdefault(name, VectorFile())

    def rb(n):
        return bytes(rng.randrange(256) for _ in range(n))

    # Keccak-256.
    for n in list(range(0, 600)) + [1087, 1088, 1089, 4096, 65536, 100000]:
        keccak_case(f("keccak-generated.bin"), keccak, f"length_{n}", rb(n))
    for n in (0, 135, 136, 137):
        keccak_case(f("keccak-generated.bin"), keccak, f"zeros_{n}", bytes(n))
        keccak_case(f("keccak-generated.bin"), keccak, f"ones_{n}", b"\xff" * n)

    # HMAC-SHA-256.
    for group in json.loads(fetch(out, "hmac_sha256_test.json"))["testGroups"]:
        for t in group["tests"]:
            if t["result"] == "valid":
                hmac_case(f("hmac-wycheproof.bin"), f"wycheproof/{t['tcId']}", hexb(t["key"]), hexb(t["msg"]), hexb(t["tag"]))
    for kl in (0, 1, 31, 32, 33, 63, 64, 65, 100, 131, 200):
        for ml in (0, 1, 31, 32, 55, 56, 63, 64, 65, 119, 120, 128, 300, 1000):
            hmac_case(f("hmac-generated.bin"), f"key_{kl}_message_{ml}", rb(kl), rb(ml))

    # HKDF-SHA-256.
    for group in json.loads(fetch(out, "hkdf_sha256_test.json"))["testGroups"]:
        for t in group["tests"]:
            want = hexb(t["okm"]) if t["result"] == "valid" else None
            if t["result"] != "valid" and t["size"] <= 255 * 32:
                fail(f"hkdf wycheproof {t['tcId']}: an invalid case of a valid size")
            hkdf_case(f("hkdf-wycheproof.bin"), f"wycheproof/{t['tcId']}", hexb(t["salt"]), hexb(t["ikm"]), hexb(t["info"]),
                      t["size"], want)
    for length in (0, 1, 16, 31, 32, 33, 64, 100, 255 * 32, 255 * 32 + 1):
        for il in (0, 1, 50, 200):
            hkdf_case(f("hkdf-generated.bin"), f"length_{length}_info_{il}", rb(rng.choice((0, 13, 32, 80))), rb(22), rb(il), length)

    # AES-128: the NIST block cipher known answers, as one CTR block over zeros.
    with zipfile.ZipFile(io.BytesIO(fetch(out, "KAT_AES.zip"))) as z:
        for name in ("ECBGFSbox128.rsp", "ECBKeySbox128.rsp", "ECBVarKey128.rsp", "ECBVarTxt128.rsp"):
            for r in rsp_sections(z.read(name).decode()):
                if r.get("_mode") == "ENCRYPT" and "CIPHERTEXT" in r:
                    ctr_case(f("aes-kat.bin"), f"{name}/{r['COUNT']}", hexb(r["KEY"]), hexb(r["PLAINTEXT"]), bytes(16),
                             hexb(r["CIPHERTEXT"]))
    for n in list(range(0, 70)) + [127, 128, 129, 255, 256, 1000, 4096]:
        ctr_case(f("aes-ctr-generated.bin"), f"length_{n}", rb(16), rb(16), rb(n))
    for low in (b"\xff" * 16, b"\x00" * 8 + b"\xff" * 8, rb(12) + b"\xff\xff\xff\xfe"):
        ctr_case(f("aes-ctr-generated.bin"), f"wrap_{low.hex()}", rb(16), low, rb(100))

    # AES-128-GCM.
    with zipfile.ZipFile(io.BytesIO(fetch(out, "gcmtestvectors.zip"))) as z:
        for name in ("gcmEncryptExtIV128.rsp", "gcmDecrypt128.rsp"):
            for r in rsp_sections(z.read(name).decode()):
                if r.get("_IVlen") != "96" or r.get("_Taglen") != "128" or "Key" not in r:
                    continue
                key, iv, aad = hexb(r["Key"]), hexb(r["IV"]), hexb(r.get("AAD", ""))
                ct, tag = hexb(r.get("CT", "")), hexb(r["Tag"])
                label = f"{name}/{r['_PTlen']}/{r['_AADlen']}/{r['Count']}"
                if r.get("FAIL"):
                    gcm_case(f("gcm-cavp.bin"), label, key, iv, b"", aad, ct + tag, valid=False)
                else:
                    gcm_case(f("gcm-cavp.bin"), label, key, iv, hexb(r.get("PT", "")), aad, ct + tag)
    for group in json.loads(fetch(out, "aes_gcm_test.json"))["testGroups"]:
        if group["keySize"] != 128 or group["ivSize"] != 96 or group["tagSize"] != 128:
            continue
        for t in group["tests"]:
            key, iv, aad, msg = hexb(t["key"]), hexb(t["iv"]), hexb(t["aad"]), hexb(t["msg"])
            sealed = hexb(t["ct"]) + hexb(t["tag"])
            gcm_case(f("gcm-wycheproof.bin"), f"wycheproof/{t['tcId']}", key, iv, msg, aad, sealed, valid=t["result"] == "valid")
    for n in list(range(0, 50)) + [63, 64, 65, 255, 256, 1000, 1280]:
        for al in (0, 1, 16, 17, 32, 70):
            key, iv, pt, aad = rb(16), rb(12), rb(n), rb(al)
            gcm_case(f("gcm-generated.bin"), f"length_{n}_aad_{al}", key, iv, pt, aad)
            sealed = bytearray(AESGCM(key).encrypt(iv, pt, aad))
            i = rng.randrange(len(sealed))
            sealed[i] ^= 1 << rng.randrange(8)
            gcm_case(f("gcm-generated.bin"), f"length_{n}_aad_{al}_flipped_{i}", key, iv, b"", aad, bytes(sealed), valid=False)
    key, iv = rb(16), rb(12)
    gcm_case(f("gcm-generated.bin"), "short_sealed", key, iv, b"", b"", rb(15), valid=False)

    # secp256k1: keys.
    g = f("secp256k1-generated.bin")
    edges = [1, 2, 3, N - 1, N - 2, (N - 1) // 2, (N + 1) // 2, 1 << 255, (1 << 128) + 1]
    bad = [0, N, N + 1, (1 << 256) - 1]
    privs = [k.to_bytes(32, "big") for k in edges] + [rb(32) for _ in range(200)]
    for i, k in enumerate(privs + [k.to_bytes(32, "big") for k in bad]):
        pub_case(g, ref, f"public_key_{i}", k)
    pubs = [ref.public_key(k) for k in privs]
    for i, pub in enumerate(pubs):
        decompress_case(g, ref, f"decompress_{i}", pub)
    for prefix in (0, 1, 4, 5, 6, 7, 0xFF):
        decompress_case(g, ref, f"decompress_prefix_{prefix:02x}", bytes([prefix]) + pubs[0][1:])
    for x in (0, 1, P - 1, P, P + 1, (1 << 256) - 1) + tuple(rng.randrange(P) for _ in range(40)):
        for prefix in (2, 3):
            decompress_case(g, ref, f"decompress_x_{x:x}_{prefix}", bytes([prefix]) + x.to_bytes(32, "big"))

    # secp256k1: ECDH.
    for i in range(100):
        ecdh_case(g, ref, f"ecdh_{i}", pubs[rng.randrange(len(pubs))], privs[rng.randrange(len(privs))])
    for k in bad:
        ecdh_case(g, ref, f"ecdh_bad_private_{k:x}", pubs[0], k.to_bytes(32, "big"))
    for x in (P, (1 << 256) - 1, 5):
        ecdh_case(g, ref, f"ecdh_bad_public_{x:x}", b"\x02" + x.to_bytes(32, "big"), privs[0])
    ecdh_case(g, ref, "ecdh_bad_public_prefix", b"\x04" + pubs[0][1:], privs[0])

    # secp256k1: sign and verify.
    hashes_ = [bytes(32), b"\xff" * 32, N.to_bytes(32, "big"), (N - 1).to_bytes(32, "big"), (N + 5).to_bytes(32, "big")]
    hashes_ += [rb(32) for _ in range(150)]
    sigs = []
    for i, msg in enumerate(hashes_):
        priv = privs[i % len(privs)]
        sigs.append((priv, msg, sign_case(g, ref, f"sign_{i}", priv, msg)))
    for k in bad:
        sign_case(g, ref, f"sign_bad_private_{k:x}", k.to_bytes(32, "big"), hashes_[5])
    for i, (priv, msg, sig) in enumerate(sigs):
        pub = ref.public_key(priv)
        verify_case(g, ref, f"verify_{i}", pub, msg, sig)
        r, s = int.from_bytes(sig[:32], "big"), int.from_bytes(sig[32:], "big")
        verify_case(g, ref, f"verify_{i}_high_s", pub, msg, sig[:32] + (N - s).to_bytes(32, "big"))
        flipped = bytearray(sig)
        flipped[rng.randrange(64)] ^= 1 << rng.randrange(8)
        verify_case(g, ref, f"verify_{i}_flipped", pub, msg, bytes(flipped))
        verify_case(g, ref, f"verify_{i}_other_hash", pub, rb(32), sig)
        if i < 10:
            for rr, ss in ((0, s), (r, 0), (N, s), (r, N), (N + r, s), (r, N + s)):
                if rr >> 256 or ss >> 256:
                    continue
                verify_case(g, ref, f"verify_{i}_r_{rr:x}_s_{ss:x}", pub, msg, rr.to_bytes(32, "big") + ss.to_bytes(32, "big"))
    verify_case(g, ref, "verify_bad_public", b"\x02" + P.to_bytes(32, "big"), hashes_[5], sigs[5][2])

    # Wycheproof ECDSA, in P1363 form: 64 bytes r || s.
    w = f("ecdsa-wycheproof.bin")
    for group in json.loads(fetch(out, "ecdsa_secp256k1_sha256_p1363_test.json"))["testGroups"]:
        point = hexb(group["publicKey"]["uncompressed"])
        pub = bytes([2 | (point[64] & 1)]) + point[1:33]
        if ref.decompress(pub) != point[1:]:
            continue
        for t in group["tests"]:
            sig = hexb(t["sig"])
            if len(sig) != 64:
                continue
            msg = hashlib.sha256(hexb(t["msg"])).digest()
            s = int.from_bytes(sig[32:], "big")
            # libsecp256k1 refuses high S, which Wycheproof's plain ECDSA accepts.
            want = None if s > N // 2 else (OK, int(t["result"] in ("valid", "acceptable")))
            verify_case(w, ref, f"wycheproof/{t['tcId']}", pub, msg, sig, want)

    # Wycheproof ECDH: the public keys that the compressed form can carry.
    e = f("ecdh-wycheproof.bin")
    for group in json.loads(fetch(out, "ecdh_secp256k1_test.json"))["testGroups"]:
        for t in group["tests"]:
            der = hexb(t["public"])
            m = re.search(rb"\x03(.)\x00(\x04.{64}|[\x02\x03].{32})$", der, re.S)
            if not m or t["result"] == "invalid":
                continue
            raw = m.group(2)
            pub = raw if len(raw) == 33 else bytes([2 | (raw[64] & 1)]) + raw[1:33]
            priv = int(t["private"], 16)
            if not 0 < priv < N or ref.decompress(pub) is None:
                continue
            status, shared = ref.ecdh(pub, priv.to_bytes(32, "big"))
            if shared[1:] != hexb(t["shared"]):
                fail(f"ecdh wycheproof {t['tcId']}: libsecp256k1 does not give the official shared x")
            ecdh_case(e, ref, f"wycheproof/{t['tcId']}", pub, priv.to_bytes(32, "big"))

    # devp2p: the discv5 primitives and the ENR example.
    d = f("devp2p.bin")
    v = md_values(fetch(out, "discv5-wire-test-vectors.md").decode())
    ecdh_case(d, ref, "discv5/ecdh", hexb(v["public-key"]), hexb(v["secret-key"]), hexb(v["shared-secret"]))
    status, secret = ref.ecdh(hexb(v["dest-pubkey"]), hexb(v["ephemeral-key"]))
    ecdh_case(d, ref, "discv5/key-derivation/ecdh", hexb(v["dest-pubkey"]), hexb(v["ephemeral-key"]))
    info = b"discovery v5 key agreement" + hexb(v["node-id-a"]) + hexb(v["node-id-b"])
    hkdf_case(d, "discv5/key-derivation/hkdf", hexb(v["challenge-data"]), secret, info, 32,
              hexb(v["initiator-key"]) + hexb(v["recipient-key"]))
    ephemeral_pubkey = hexb(v["ephemeral-pubkey"])
    signed = hashlib.sha256(b"discovery v5 identity proof" + hexb(v["challenge-data"]) + ephemeral_pubkey + hexb(v["node-id-B"])).digest()
    sig = sign_case(d, ref, "discv5/id-nonce-signing", hexb(v["static-key"]), signed, hexb(v["id-signature"]))
    verify_case(d, ref, "discv5/id-nonce-verify", ref.public_key(hexb(v["static-key"])), signed, sig, (OK, 1))
    gcm_case(d, "discv5/encryption", hexb(v["encryption-key"]), hexb(v["nonce"]), hexb(v["pt"]), hexb(v["ad"]),
             hexb(v["message-ciphertext"]))
    enr_text = fetch(out, "enr.md").decode()
    record_b64 = re.search(r"(enr:[-_A-Za-z0-9]+)", enr_text).group(1)[4:]
    record = base64.urlsafe_b64decode(record_b64 + "=" * (-len(record_b64) % 4))
    priv = hexb(re.search(r"private key:\s*\n\s*([0-9a-f]{64})", enr_text).group(1))
    node_id = hexb(re.search(r"node ID is `([0-9a-f]{64})`", enr_text).group(1))
    items = rlp_decode_list(record)
    fields = dict(zip(items[2::2], items[3::2]))
    pub = fields[b"secp256k1"]
    if ref.public_key(priv) != pub:
        fail("enr: the private key does not give the record's key")
    pub_case(d, ref, "enr/public-key", priv)
    decompress_case(d, ref, "enr/decompress", pub)
    keccak_case(d, keccak, "enr/node-id", ref.decompress(pub), node_id)
    content_hash = bytes(keccak(1088, 512, bytearray(rlp_encode_list(items[1:])), 0x01, 32))
    keccak_case(d, keccak, "enr/content-hash", rlp_encode_list(items[1:]))
    verify_case(d, ref, "enr/verify", pub, content_hash, items[0], (OK, 1))
    if ref.sign(priv, content_hash)[1] == items[0]:
        sign_case(d, ref, "enr/sign", priv, content_hash, items[0])

    # ChaCha20-Poly1305: RFC 8439 sections 2.8.2 and A.5.
    c = f("chacha20-poly1305-rfc.bin")
    rfc8439 = fetch(out, "rfc8439.txt").decode()
    sec = rfc_section(rfc8439, "2.8.2.  Example and Test Vector for AEAD_CHACHA20_POLY1305", "3.  Implementation Advice")
    nonce = rfc_dump(sec, "32-bit fixed-common part:") + rfc_dump(sec, "IV:")
    chacha_case(c, "rfc8439/2.8.2", rfc_dump(sec, "Key:"), nonce, rfc_dump(sec, "Plaintext:"), rfc_dump(sec, "AAD:"),
                rfc_dump(sec, "Ciphertext:") + rfc_dump(sec, "Tag:"))
    sec = rfc_section(rfc8439, "A.5.  ChaCha20-Poly1305 AEAD Decryption", "Appendix B.  Performance Measurements")
    sealed = rfc_dump(sec, "Ciphertext:") + rfc_dump(sec, "Received Tag:")
    chacha_case(c, "rfc8439/A.5", rfc_dump(sec, "The ChaCha20 Key"), rfc_dump(sec, "The nonce:"), rfc_dump(sec, "Plaintext::"),
                rfc_dump(sec, "The AAD:"), sealed)

    # Poly1305: RFC 8439 sections 2.5.2 and A.3.
    pr = f("poly1305-rfc.bin")
    sec = rfc_section(rfc8439, "2.5.2.  Poly1305 Example and Test Vector", "2.6.  Generating the Poly1305 Key Using ChaCha20")
    key = bytes.fromhex(re.sub(r"[^0-9a-f]", "", re.search(r"Key Material: ([0-9a-f:\s]+?)o  s as", sec).group(1)))
    tag = bytes.fromhex(re.search(r"Tag: ([0-9a-f:]+)", sec).group(1).replace(":", ""))
    poly1305_case(pr, "rfc8439/2.5.2", key, rfc_dump(sec, "Message to be Authenticated:"), tag)
    sec = rfc_section(rfc8439, "A.3.  Poly1305 Message Authentication Code", "A.4.  Poly1305 Key Generation Using ChaCha20")
    vectors = re.split(r"\n\s*Test Vector #", sec)[1:]
    if len(vectors) != 11:
        fail("rfc 8439: section A.3 does not hold 11 vectors")
    for i, v in enumerate(vectors, 1):
        if "One-time Poly1305 Key:" in v:
            key, msg, tag = rfc_dump(v, "One-time Poly1305 Key:"), rfc_dump(v, "Text to MAC:"), rfc_dump(v, "Tag:")
        else:
            key = rfc_dump(v, "R:") + rfc_dump(v, "S:")
            msg, tag = rfc_dump(v, "data:"), rfc_dump(v, "tag:")
        poly1305_case(pr, f"rfc8439/A.3/{i}", key, msg, tag)
    pg = f("poly1305-generated.bin")
    for n in list(range(0, 100)) + [255, 256, 257, 1000, 4096]:
        poly1305_case(pg, f"length_{n}", rb(32), rb(n))
    for n in (0, 15, 16, 17, 64):
        poly1305_case(pg, f"ones_{n}", b"\xff" * 32, b"\xff" * n)

    # ChaCha20-Poly1305: Wycheproof, 256-bit keys, 96-bit nonces, 128-bit tags.
    for group in json.loads(fetch(out, "chacha20_poly1305_test.json"))["testGroups"]:
        if group["keySize"] != 256 or group["ivSize"] != 96 or group["tagSize"] != 128:
            continue
        for t in group["tests"]:
            sealed = hexb(t["ct"]) + hexb(t["tag"])
            chacha_case(f("chacha20-poly1305-wycheproof.bin"), f"wycheproof/{t['tcId']}", hexb(t["key"]), hexb(t["iv"]),
                        hexb(t["msg"]), hexb(t["aad"]), sealed, valid=t["result"] == "valid")

    # ChaCha20-Poly1305: generated lengths and flipped bits.
    g = f("chacha20-poly1305-generated.bin")
    for n in list(range(0, 140)) + [255, 256, 257, 511, 512, 513, 1000, 1280, 4096, 65535, 65536, 100000]:
        for al in ((0, 1, 15, 16, 17, 70) if n < 140 else (0, 13)):
            key, nonce, pt, aad = rb(32), rb(12), rb(n), rb(al)
            chacha_case(g, f"length_{n}_aad_{al}", key, nonce, pt, aad)
            sealed = bytearray(ChaCha20Poly1305(key).encrypt(nonce, pt, aad))
            i = rng.randrange(len(sealed))
            sealed[i] ^= 1 << rng.randrange(8)
            chacha_case(g, f"length_{n}_aad_{al}_flipped_{i}", key, nonce, b"", aad, bytes(sealed), valid=False)
    key, nonce = rb(32), rb(12)
    for n in range(16):
        chacha_case(g, f"short_sealed_{n}", key, nonce, b"", b"", rb(n), valid=False)
    for n in (0, 64):
        pt = rb(n)
        sealed = ChaCha20Poly1305(key).encrypt(nonce, pt, b"\x01")
        chacha_case(g, f"other_aad_{n}", key, nonce, b"", b"\x02", sealed, valid=False)

    # X25519: RFC 7748 sections 5.2 and 6.1, with the iterations to 1000.
    x = f("x25519-rfc.bin")
    singles, iters, dh = rfc7748_x25519(fetch(out, "rfc7748.txt").decode())
    if len(singles) != 2 or len(dh) != 5 or [k for k, _ in iters][:2] != [1, 1000]:
        fail("rfc 7748: the X25519 test vectors do not parse")
    for i, (scalar, u, want) in enumerate(singles):
        x25519_case(x, f"rfc7748/5.2/{i}", scalar, u, (OK, want))
    k = u = (9).to_bytes(32, "little")
    want = dict(iters)
    for i in range(1, 1001):
        k, u = x25519_case(x, f"rfc7748/5.2/iteration_{i}", k, u, (OK, want[i]) if i in want else None), k
    nine = (9).to_bytes(32, "little")
    x25519_case(x, "rfc7748/6.1/alice_public", dh["Alice's private key, a"], nine, (OK, dh["Alice's public key, X25519(a, 9)"]))
    x25519_case(x, "rfc7748/6.1/bob_public", dh["Bob's private key, b"], nine, (OK, dh["Bob's public key, X25519(b, 9)"]))
    x25519_case(x, "rfc7748/6.1/alice_shared", dh["Alice's private key, a"], dh["Bob's public key, X25519(b, 9)"],
                (OK, dh["Their shared secret, K"]))
    x25519_case(x, "rfc7748/6.1/bob_shared", dh["Bob's private key, b"], dh["Alice's public key, X25519(a, 9)"],
                (OK, dh["Their shared secret, K"]))

    # X25519: Wycheproof. An all-zero shared value is the zero status.
    for group in json.loads(fetch(out, "x25519_test.json"))["testGroups"]:
        if group["curve"] != "curve25519":
            continue
        for t in group["tests"]:
            shared = hexb(t["shared"])
            want = (X25519_ZERO, None) if shared == bytes(32) else (OK, shared)
            x25519_case(f("x25519-wycheproof.bin"), f"wycheproof/{t['tcId']}", hexb(t["private"]), hexb(t["public"]), want)

    # X25519: generated scalars and points, public keys, and u at the edges.
    g = f("x25519-generated.bin")
    p25519 = 2**255 - 19
    for i in range(200):
        a, b = rb(32), rb(32)
        pa = x25519_case(g, f"public_{i}_a", a, nine)
        pb = x25519_case(g, f"public_{i}_b", b, nine)
        s1 = x25519_case(g, f"shared_{i}_ab", a, pb)
        s2 = x25519_case(g, f"shared_{i}_ba", b, pa)
        if s1 != s2:
            fail("x25519: the two sides do not agree")
    for v in (0, 1, 2, p25519 - 1, p25519, p25519 + 1, p25519 + 9, 2**255 - 1, 2**255, 2**256 - 1, 2**255 + 9) + \
            tuple(rng.randrange(2**256) for _ in range(40)):
        x25519_case(g, f"u_{v:x}", rb(32), v.to_bytes(32, "little"))
    for scalar in (bytes(32), b"\xff" * 32, b"\x01" + bytes(31), bytes(31) + b"\x80"):
        x25519_case(g, f"scalar_{scalar.hex()}", scalar, rb(32))

    # P-256: RFC 6979 section A.2.5, SHA-256.
    r6 = f("p256-rfc6979.bin")
    priv, pub, sigs = rfc6979_p256(fetch(out, "rfc6979.txt").decode())
    p256_pub_case(r6, "rfc6979/A.2.5/public_key", priv, pub)
    for msg, sig in sigs:
        h = hashlib.sha256(msg).digest()
        p256_sign_case(r6, f"rfc6979/A.2.5/{msg.decode()}", priv, h, sig)
        p256_verify_case(r6, f"rfc6979/A.2.5/{msg.decode()}/verify", pub, h, sig, (OK, 1))

    # P-256: NIST CAVP FIPS 186-4 KeyPair, PKV, SigGen (as checks) and SigVer, P-256 with SHA-256.
    cv = f("p256-cavp.bin")
    with zipfile.ZipFile(io.BytesIO(fetch(out, "186-4ecdsatestvectors.zip"))) as z:
        def rsp(name):
            return cavp_ecdsa(z.read("186-4ecdsatestvectors/" + name).decode())
        some_hash, some_sig = hashlib.sha256(b"pkv").digest(), b"\x01" * 64
        for i, r in enumerate(x for x in rsp("KeyPair.rsp") if x["_section"] == "P-256" and "d" in x):
            want = b"\x04" + int(r["Qx"], 16).to_bytes(32, "big") + int(r["Qy"], 16).to_bytes(32, "big")
            p256_pub_case(cv, f"keypair/{i}", int(r["d"], 16).to_bytes(32, "big"), want)
        for i, r in enumerate(x for x in rsp("PKV.rsp") if x["_section"] == "P-256" and "Result" in x):
            point = cavp_point(r)
            if point is None:
                continue
            ok = r["Result"].startswith("P")
            p256_verify_case(cv, f"pkv/{i}", point, some_hash, some_sig, (OK, 0) if ok else (INVALID_PUBLIC_KEY, 0))
        for name in ("SigGen.rsp", "SigVer.rsp"):
            for i, r in enumerate(x for x in rsp(name) if x["_section"] == "P-256,SHA-256" and "Msg" in x):
                point = cavp_point(r)
                h = hashlib.sha256(hexb(r["Msg"])).digest()
                sig = int(r["R"], 16).to_bytes(32, "big") + int(r["S"], 16).to_bytes(32, "big")
                want = (OK, 1) if name == "SigGen.rsp" or r["Result"].startswith("P") else (OK, 0)
                if point is None:
                    continue
                p256_verify_case(cv, f"{name[:-4].lower()}/{i}", point, h, sig, want)

    # P-256: Wycheproof ECDSA, in P1363 form: 64 bytes r || s.
    w = f("p256-wycheproof.bin")
    for group in json.loads(fetch(out, "ecdsa_secp256r1_sha256_p1363_test.json"))["testGroups"]:
        point = hexb(group["publicKey"]["uncompressed"])
        for t in group["tests"]:
            sig = hexb(t["sig"])
            if len(sig) != 64:
                continue
            h = hashlib.sha256(hexb(t["msg"])).digest()
            p256_verify_case(w, f"wycheproof/{t['tcId']}", point, h, sig, (OK, int(t["result"] == "valid")))

    # P-256: generated keys, signatures and checks.
    g = f("p256-generated.bin")
    edges = [1, 2, 3, P256_N - 1, P256_N - 2, (P256_N - 1) // 2, (P256_N + 1) // 2, 1 << 255, (1 << 128) + 1]
    bad = [0, P256_N, P256_N + 1, (1 << 256) - 1]
    privs = [k.to_bytes(32, "big") for k in edges] + [rb(32) for _ in range(150)]
    for i, k in enumerate(privs + [k.to_bytes(32, "big") for k in bad]):
        p256_pub_case(g, f"public_key_{i}", k)
    privs = [k for k in privs if P256.private(k) is not None]
    hashes_ = [bytes(32), b"\xff" * 32, P256_N.to_bytes(32, "big"), (P256_N - 1).to_bytes(32, "big"),
               (P256_N + 5).to_bytes(32, "big")] + [rb(32) for _ in range(150)]
    for i, h in enumerate(hashes_):
        priv = privs[i % len(privs)]
        pub = P256.public_key(priv)
        sig = p256_sign_case(g, f"sign_{i}", priv, h)
        p256_verify_case(g, f"verify_{i}", pub, h, sig, (OK, 1))
        r, s = int.from_bytes(sig[:32], "big"), int.from_bytes(sig[32:], "big")
        p256_verify_case(g, f"verify_{i}_negated_s", pub, h, sig[:32] + (P256_N - s).to_bytes(32, "big"), (OK, 1))
        flipped = bytearray(sig)
        flipped[rng.randrange(64)] ^= 1 << rng.randrange(8)
        p256_verify_case(g, f"verify_{i}_flipped", pub, h, bytes(flipped))
        p256_verify_case(g, f"verify_{i}_other_hash", pub, rb(32), sig)
        if i < 10:
            for rr, ss in ((0, s), (r, 0), (P256_N, s), (r, P256_N), (P256_N + r, s), (r, P256_N + s)):
                if rr >> 256 or ss >> 256:
                    continue
                p256_verify_case(g, f"verify_{i}_r_{rr:x}_s_{ss:x}", pub, h, rr.to_bytes(32, "big") + ss.to_bytes(32, "big"), (OK, 0))
    for k in bad:
        p256_sign_case(g, f"sign_bad_private_{k:x}", k.to_bytes(32, "big"), hashes_[5])
    pub = P256.public_key(privs[0])
    sig = P256.sign(privs[0], hashes_[5])[1]
    for prefix in (0, 2, 3, 5, 6, 7, 0xFF):
        p256_verify_case(g, f"verify_prefix_{prefix:02x}", bytes([prefix]) + pub[1:], hashes_[5], sig, (INVALID_PUBLIC_KEY, 0))
    for xv, yv in ((P256_P, 1), (1, P256_P), ((1 << 256) - 1, 0), (0, 0)) + tuple((rng.randrange(P256_P), rng.randrange(P256_P)) for _ in range(20)):
        p256_verify_case(g, f"verify_point_{xv:x}_{yv:x}", b"\x04" + xv.to_bytes(32, "big") + yv.to_bytes(32, "big"), hashes_[5], sig)
    for xv in range(1, 40):
        yv = p256_sqrt((xv ** 3 - 3 * xv + 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B) % P256_P)
        if yv is None:
            continue
        point = b"\x04" + xv.to_bytes(32, "big") + yv.to_bytes(32, "big")
        p256_verify_case(g, f"verify_small_x_{xv}", point, hashes_[5], sig, (OK, 0))
        point = b"\x04" + (xv + P256_P).to_bytes(32, "big") + yv.to_bytes(32, "big")
        p256_verify_case(g, f"verify_small_x_{xv}_plus_p", point, hashes_[5], sig, (INVALID_PUBLIC_KEY, 0))
    for yv in range(1, 40):
        xv = p256_x_of_y(yv)
        if xv is None:
            continue
        point = b"\x04" + xv.to_bytes(32, "big") + yv.to_bytes(32, "big")
        p256_verify_case(g, f"verify_small_y_{yv}", point, hashes_[5], sig, (OK, 0))
        point = b"\x04" + xv.to_bytes(32, "big") + (yv + P256_P).to_bytes(32, "big")
        p256_verify_case(g, f"verify_small_y_{yv}_plus_p", point, hashes_[5], sig, (INVALID_PUBLIC_KEY, 0))
    x0, y0 = int.from_bytes(pub[1:33], "big"), int.from_bytes(pub[33:], "big")
    for name, point in (("x_plus_p", (x0 + P256_P, y0)), ("y_plus_p", (x0, y0 + P256_P)), ("negated_y", (x0, P256_P - y0))):
        if point[0] >> 256 or point[1] >> 256:
            continue
        p256_verify_case(g, f"verify_{name}", b"\x04" + point[0].to_bytes(32, "big") + point[1].to_bytes(32, "big"), hashes_[5], sig)

    manifest = []
    for name in sorted(files):
        path = os.path.join(out, name)
        files[name].write(path)
        with open(path, "rb") as fh:
            digest = hashlib.sha256(fh.read()).hexdigest()
        manifest.append(f"{name} {len(files[name].cases)} {digest}")
        print(f"{name}: {len(files[name].cases)} cases")
    with open(os.path.join(out, "manifest-primitives.txt"), "w") as fh:
        fh.write("\n".join(manifest) + "\n")


if __name__ == "__main__":
    main(sys.argv[1])
