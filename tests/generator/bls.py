"""
Write the vector files for BLS12-381: the signatures, the points and the
hash to G2.

Usage: python3 -I bls.py OUT_DIR

Sources:
- Official cases: tests/cryptography/bls and tests/cryptography/hash_to_curve
  of ethereum/cryptography-specs at the pinned commit, which run.sh fetches
  into OUT_DIR/sources/cryptography-specs. Each file is checked
  against the pinned SHA256SUMS of its directory, and each SHA256SUMS against
  its pinned SHA-256.
- Generated cases: the pinned py_arkworks_bls12381 (the BLS library that
  consensus-specs pins) for the points, the hash to G2, the pairing check and
  the subgroup checks; the steps of EthLib/Cryptography/Bls/Signatures.lean
  and Compress.lean, written out here, combine them. expand_message_xmd
  follows RFC 9380 section 5.3.1 with hashlib.
- The script stops when the reference disagrees with an official case or with
  the rules written out here.
The file format is in README.md.
"""

import hashlib
import os
import random
import struct
import sys

import yaml
from py_arkworks_bls12381 import G1Point, G2Point, GT, Scalar

COMMIT = "bb6dfe55198243682bc2eaf94611af2dbce1be6f"   # ethereum/cryptography-specs v0.3.0, fetched by run.sh
SUMS = {
    "bls": "beab1a4d6a7a32ab411850846500f20d592cacdbf541425efcfa311ac116d3cf",
    "hash_to_curve": "53a976d2f3c28548518ead50f32e6ccd4b90f0e969d933060afff157ba875933",
}

# include/crypto.inc and include/bls12381.inc
OK, INVALID_PRIVATE_KEY, INVALID_PUBLIC_KEY = 0, 4, 5
INVALID_SIGNATURE, EMPTY_LIST, INVALID_ENCODING, XMD_LENGTH, POINT_AT_INFINITY = 8, 9, 10, 11, 12
# tests/generator/README.md, primitive file kinds
K_SK_TO_PK, K_SIGN, K_VERIFY, K_AGGREGATE, K_FAST, K_KEY_VALIDATE, K_ETH_AGGREGATE, K_ETH_FAST = range(22, 30)
K_G1_DECODE, K_G2_DECODE, K_G1_ADD, K_G1_NEG, K_XMD, K_HASH_TO_G2 = range(30, 36)

P = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
R = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
DST = b"BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_"
QUUX = b"QUUX-V01-CS02-with-BLS12381G2_XMD:SHA-256_SSWU_RO_"
G1_INF = b"\xc0" + bytes(47)
G2_INF = b"\xc0" + bytes(95)

out_dir = sys.argv[1]
sources = os.path.join(out_dir, "sources", "cryptography-specs", "tests", "cryptography")


def fetch(path, digest):
    """The bytes of tests/cryptography/<path>, checked against digest."""
    data = open(os.path.join(sources, path), "rb").read()
    if hashlib.sha256(data).hexdigest() != digest:
        raise SystemExit(f"bls.py: {path}: SHA-256 does not match its pin")
    return data


def official(directory):
    """(handler, case, parsed data.yaml) for every case of a pinned directory."""
    sums = fetch(f"{directory}/SHA256SUMS", SUMS[directory]).decode()
    for line in sums.splitlines():
        if not line or line.startswith("#"):
            continue
        digest, path = line.split()
        handler, case = path.split("/")[:2]
        yield handler, case, yaml.safe_load(fetch(f"{directory}/{path}", digest))


def hx(s):
    s = str(s)
    return bytes.fromhex(s[2:] if s.startswith("0x") else s)


# ---------------------------------------------------------------- Fp and Fp2, for the rules of Compress.lean

def fp_sqrt(a):
    s = pow(a, (P + 1) // 4, P)
    return s if s * s % P == a % P else None


def f2_mul(a, b):
    return ((a[0] * b[0] - a[1] * b[1]) % P, (a[0] * b[1] + a[1] * b[0]) % P)


def f2_sqrt(a):
    """Fp2.sqrt of Compress.lean."""
    a0, a1 = a
    if a1 == 0:
        s = fp_sqrt(a0)
        if s is not None:
            return (s, 0)
        s = fp_sqrt(-a0 % P)
        return None if s is None else (0, s)
    s = fp_sqrt((a0 * a0 + a1 * a1) % P)
    if s is None:
        return None
    inv2 = pow(2, P - 2, P)
    c0 = fp_sqrt((a0 + s) * inv2 % P)
    if c0 is None:
        c0 = fp_sqrt((a0 - s) * inv2 % P)
    if c0 is None:
        return None
    return (c0, a1 * pow(2 * c0, P - 2, P) % P)


def sign_bit(y):
    return y > P - y


def g1_uncompress(b):
    """(x, y) or 'inf' when G1.uncompress accepts b, else None."""
    if len(b) != 48 or not b[0] & 0x80:
        return None
    if b[0] & 0x40:
        return "inf" if b[0] == 0xC0 and not any(b[1:]) else None
    x = int.from_bytes(bytes([b[0] & 0x1F]) + b[1:], "big")
    if x >= P:
        return None
    y = fp_sqrt((x * x * x + 4) % P)
    if y is None:
        return None
    return (x, y if sign_bit(y) == bool(b[0] & 0x20) else P - y)


def g2_uncompress(b):
    """((x0, x1), (y0, y1)) or 'inf' when G2.uncompress accepts b, else None."""
    if len(b) != 96 or not b[0] & 0x80:
        return None
    if b[0] & 0x40:
        return "inf" if b[0] == 0xC0 and not any(b[1:]) else None
    x1 = int.from_bytes(bytes([b[0] & 0x1F]) + b[1:48], "big")
    x0 = int.from_bytes(b[48:], "big")
    if x1 >= P or x0 >= P:
        return None
    x = (x0, x1)
    rhs = f2_mul(f2_mul(x, x), x)
    y = f2_sqrt(((rhs[0] + 4) % P, (rhs[1] + 4) % P))
    if y is None:
        return None
    big = sign_bit(y[1]) if y[1] else sign_bit(y[0])
    return (x, y if big == bool(b[0] & 0x20) else ((-y[0]) % P, (-y[1]) % P))


def fp_bytes(v):
    return v.to_bytes(48, "big")


# ---------------------------------------------------------------- the reference, with the steps of Signatures.lean

def ark_g1(b):
    """The point of an encoding that G1.uncompress accepts, without the subgroup check."""
    return G1Point.from_compressed_bytes_unchecked(b)


def ark_g2(b):
    return G2Point.from_compressed_bytes_unchecked(b)


def g1_decode(b):
    """decodeG1Export: the compressed point again, or None."""
    if g1_uncompress(b) is None:
        return None
    p = ark_g1(b)
    return bytes(p.to_compressed_bytes()) if p.is_in_subgroup() else None


def g2_decode(b):
    if g2_uncompress(b) is None:
        return None
    p = ark_g2(b)
    return bytes(p.to_compressed_bytes()) if p.is_in_subgroup() else None


def key_validate(b):
    u = g1_uncompress(b)
    if u is None or u == "inf":
        return None
    p = ark_g1(b)
    return p if p.is_in_subgroup() else None


def hash_to_g2(msg, dst):
    point = G2Point.hash_to_curve(msg, dst)
    if len(dst) > 255:                          # RFC 9380 section 5.3.3: the reference must shorten a long DST
        short = hashlib.sha256(b"H2C-OVERSIZE-DST-" + dst).digest()
        agree("long DST", bytes(point.to_compressed_bytes()),
              bytes(G2Point.hash_to_curve(msg, short).to_compressed_bytes()))
    return point


def verify(pk, msg, sig):
    """coreVerify with the message tag."""
    if g2_uncompress(sig) is None:
        return False
    r = ark_g2(sig)
    if not r.is_in_subgroup():
        return False
    p = key_validate(pk)
    if p is None:
        return False
    return GT.pairing_check([G1Point(), -p], [r, hash_to_g2(msg, DST)])


def sign(sk, msg):
    if not 0 < sk < R:
        return None
    return bytes((hash_to_g2(msg, DST) * Scalar(sk)).to_compressed_bytes())


def sk_to_pk(sk):
    if not 0 < sk < R:
        return None
    return bytes((G1Point() * Scalar(sk)).to_compressed_bytes())


def aggregate(sigs):
    if not sigs:
        return EMPTY_LIST, None
    acc = G2Point.identity()
    for s in sigs:
        if g2_uncompress(s) is None:
            return INVALID_SIGNATURE, None
        acc = acc + ark_g2(s)
    return OK, bytes(acc.to_compressed_bytes())


def fast_aggregate_verify(pks, msg, sig):
    if not pks:
        return False
    acc = G1Point.identity()
    for pk in pks:
        p = key_validate(pk)
        if p is None:
            return False
        acc = acc + p
    return verify(bytes(acc.to_compressed_bytes()), msg, sig)


def eth_aggregate_pubkeys(pks):
    if not pks:
        return EMPTY_LIST, None
    acc = G1Point.identity()
    for pk in pks:
        p = key_validate(pk)
        if p is None:
            return INVALID_PUBLIC_KEY, None
        acc = acc + p
    return OK, bytes(acc.to_compressed_bytes())


def eth_fast_aggregate_verify(pks, msg, sig):
    if not pks:
        return sig == G2_INF
    return fast_aggregate_verify(pks, msg, sig)


def expand_message_xmd(msg, dst, n):
    """RFC 9380 section 5.3.1, with section 5.3.3 for a long DST."""
    if n > 8160:
        return None
    if len(dst) > 255:
        dst = hashlib.sha256(b"H2C-OVERSIZE-DST-" + dst).digest()
    ell = (n + 31) // 32
    dstp = dst + bytes([len(dst)])
    b0 = hashlib.sha256(bytes(64) + msg + n.to_bytes(2, "big") + b"\0" + dstp).digest()
    b = [hashlib.sha256(b0 + b"\1" + dstp).digest()]
    for i in range(2, ell + 1):
        b.append(hashlib.sha256(bytes(x ^ y for x, y in zip(b0, b[-1])) + bytes([i]) + dstp).digest())
    return b"".join(b)[:n]


def g2_affine(point):
    """x.c0, x.c1, y.c0, y.c1 of a point, from its compressed form."""
    c = bytes(point.to_compressed_bytes())
    u = g2_uncompress(c)
    if u == "inf":
        return None
    (x0, x1), (y0, y1) = u
    return fp_bytes(x0) + fp_bytes(x1) + fp_bytes(y0) + fp_bytes(y1)


# ---------------------------------------------------------------- case files

def u64(n):
    return struct.pack("<Q", n)


def blob(b):
    return u64(len(b)) + b


class CaseFile:
    def __init__(self, name):
        self.name, self.cases = name, []

    def add(self, kind, case, *fields):
        self.cases.append(u64(kind) + blob(case.encode()) + b"".join(fields))

    def write(self):
        data = b"CRYPTOV2" + u64(len(self.cases)) + b"".join(self.cases)
        with open(os.path.join(out_dir, self.name), "wb") as f:
            f.write(data)
        manifest.append(f"{self.name} {len(self.cases)} {hashlib.sha256(data).hexdigest()}")
        print(f"{self.name}: {len(self.cases)} cases")


manifest = []


def agree(case, got, want):
    if got != want:
        raise SystemExit(f"bls.py: {case}: the reference gives {got!r}, the case {want!r}")


def status_bytes(status, data, size):
    return u64(status) + (data if status == OK else bytes(size))


def add_sk_to_pk(f, case, sk_bytes):
    pk = sk_to_pk(int.from_bytes(sk_bytes, "big"))
    f.add(K_SK_TO_PK, case, sk_bytes, status_bytes(OK if pk else INVALID_PRIVATE_KEY, pk, 48))


def add_sign(f, case, sk_bytes, msg):
    sig = sign(int.from_bytes(sk_bytes, "big"), msg)
    f.add(K_SIGN, case, sk_bytes, blob(msg), status_bytes(OK if sig else INVALID_PRIVATE_KEY, sig, 96))
    return sig


def add_verify(f, case, pk, msg, sig):
    f.add(K_VERIFY, case, pk, blob(msg), sig, u64(int(verify(pk, msg, sig))))


def add_aggregate(f, case, sigs):
    st, sig = aggregate(sigs)
    f.add(K_AGGREGATE, case, blob(b"".join(sigs)), status_bytes(st, sig, 96))
    return st, sig


def add_fast(f, case, pks, msg, sig):
    f.add(K_FAST, case, blob(b"".join(pks)), blob(msg), sig, u64(int(fast_aggregate_verify(pks, msg, sig))))


def add_key_validate(f, case, pk):
    f.add(K_KEY_VALIDATE, case, pk, u64(int(key_validate(pk) is not None)))


def add_eth_aggregate(f, case, pks):
    st, pk = eth_aggregate_pubkeys(pks)
    f.add(K_ETH_AGGREGATE, case, blob(b"".join(pks)), status_bytes(st, pk, 48))
    return st, pk


def add_eth_fast(f, case, pks, msg, sig):
    f.add(K_ETH_FAST, case, blob(b"".join(pks)), blob(msg), sig, u64(int(eth_fast_aggregate_verify(pks, msg, sig))))


def add_g1_decode(f, case, b):
    d = g1_decode(b)
    f.add(K_G1_DECODE, case, b, status_bytes(OK if d else INVALID_ENCODING, d, 48))
    return d


def add_g2_decode(f, case, b):
    d = g2_decode(b)
    f.add(K_G2_DECODE, case, b, status_bytes(OK if d else INVALID_ENCODING, d, 96))
    return d


def add_xmd(f, case, msg, dst, n):
    u = expand_message_xmd(msg, dst, n)
    f.add(K_XMD, case, blob(msg), blob(dst), u64(n), u64(OK if u is not None else XMD_LENGTH), blob(u or b""))
    return u


def add_hash_to_g2(f, case, msg, dst):
    a = g2_affine(hash_to_g2(msg, dst))
    f.add(K_HASH_TO_G2, case, blob(msg), blob(dst), status_bytes(OK if a else POINT_AT_INFINITY, a, 192))
    return a


# ---------------------------------------------------------------- official cases

def fixed_sizes(handler, i):
    """True when every key, secret key and signature of a case has its fixed size."""
    if handler in ("deserialization_G1",):
        return len(hx(i["pubkey"])) == 48
    if handler in ("deserialization_G2",):
        return len(hx(i["signature"])) == 96
    if handler == "sign":
        return len(hx(i["privkey"])) == 32
    if handler == "verify":
        return len(hx(i["pubkey"])) == 48 and len(hx(i["signature"])) == 96
    if handler == "aggregate":
        return all(len(hx(s)) == 96 for s in i)
    if handler == "eth_aggregate_pubkeys":
        return all(len(hx(k)) == 48 for k in i)
    if handler in ("fast_aggregate_verify", "eth_fast_aggregate_verify"):
        return all(len(hx(k)) == 48 for k in i["pubkeys"]) and len(hx(i["signature"])) == 96
    return True


def write_official():
    f = CaseFile("bls-official.bin")
    for handler, case, d in official("bls"):
        i, o = d["input"], d["output"]
        if handler != "aggregate_verify" and not fixed_sizes(handler, i):
            print(f"left out: {handler}/{case}, a value of another size")
            continue
        if handler == "sign":
            sig = add_sign(f, case, hx(i["privkey"]), hx(i["message"]))
            agree(case, sig, None if o is None else hx(o))
        elif handler == "verify":
            agree(case, verify(hx(i["pubkey"]), hx(i["message"]), hx(i["signature"])), o)
            add_verify(f, case, hx(i["pubkey"]), hx(i["message"]), hx(i["signature"]))
        elif handler == "aggregate":
            st, sig = add_aggregate(f, case, [hx(s) for s in i])
            agree(case, sig, None if o is None else hx(o))
        elif handler == "fast_aggregate_verify":
            pks = [hx(k) for k in i["pubkeys"]]
            agree(case, fast_aggregate_verify(pks, hx(i["message"]), hx(i["signature"])), o)
            add_fast(f, case, pks, hx(i["message"]), hx(i["signature"]))
        elif handler == "eth_aggregate_pubkeys":
            st, pk = add_eth_aggregate(f, case, [hx(k) for k in i])
            agree(case, pk, None if o is None else hx(o))
        elif handler == "eth_fast_aggregate_verify":
            pks = [hx(k) for k in i["pubkeys"]]
            agree(case, eth_fast_aggregate_verify(pks, hx(i["message"]), hx(i["signature"])), o)
            add_eth_fast(f, case, pks, hx(i["message"]), hx(i["signature"]))
        elif handler == "deserialization_G1":
            d1 = add_g1_decode(f, case, hx(i["pubkey"]))
            agree(case, d1 is not None, o)
        elif handler == "deserialization_G2":
            d2 = add_g2_decode(f, case, hx(i["signature"]))
            agree(case, d2 is not None, o)
        elif handler == "aggregate_verify":
            continue                            # AggregateVerify: consensus-specs does not call it
        elif handler == "hash_to_G2":
            a = add_hash_to_g2(f, case, i["msg"].encode(), QUUX)
            want = b"".join(fp_bytes(int(v, 16)) for c in ("x", "y") for v in o[c].split(","))
            agree(case, a, want)
        else:
            raise SystemExit(f"bls.py: unknown handler {handler}")
    for handler, case, d in official("hash_to_curve"):
        i, o = d["input"], d["output"]
        if handler == "expand_message_xmd":
            u = add_xmd(f, case, hx(i["msg"]), hx(i["dst"]), i["len_in_bytes"])
            agree(case, u, hx(o))
        elif handler == "hash_to_g2":
            a = add_hash_to_g2(f, case, hx(i["msg"]), hx(i["dst"]))
            want = b"".join(fp_bytes(int(v, 16)) for c in ("x", "y") for v in o[c])
            agree(case, a, want)
        else:
            raise SystemExit(f"bls.py: unknown handler {handler}")
    f.write()


# ---------------------------------------------------------------- generated cases

def on_curve_g1(rng, in_subgroup):
    """A compressed point of E1 that is in G1 or, with overwhelming odds, not."""
    if in_subgroup:
        return bytes((G1Point() * Scalar(rng.randrange(1, R))).to_compressed_bytes())
    while True:
        x = rng.randrange(P)
        y = fp_sqrt((x * x * x + 4) % P)
        if y is not None:
            b = bytearray(fp_bytes(x))
            b[0] |= 0x80 | (0x20 if rng.random() < 0.5 else 0)
            return bytes(b)


def on_curve_g2(rng, in_subgroup):
    if in_subgroup:
        return bytes((G2Point() * Scalar(rng.randrange(1, R))).to_compressed_bytes())
    while True:
        x = (rng.randrange(P), rng.randrange(P))
        rhs = f2_mul(f2_mul(x, x), x)
        if f2_sqrt(((rhs[0] + 4) % P, (rhs[1] + 4) % P)) is not None:
            b = bytearray(fp_bytes(x[1]) + fp_bytes(x[0]))
            b[0] |= 0x80 | (0x20 if rng.random() < 0.5 else 0)
            return bytes(b)


def bad_g1(rng):
    """Encodings that G1.uncompress rejects, or that test its rules."""
    good = on_curve_g1(rng, True)
    x = int.from_bytes(bytes([good[0] & 0x1F]) + good[1:], "big")
    out = [
        ("no_compression_flag", bytes([good[0] & 0x7F]) + good[1:]),
        ("infinity_and_sign", b"\xe0" + bytes(47)),
        ("infinity_with_x", b"\xc0" + bytes(46) + b"\x01"),
        ("infinity_without_compression", b"\x40" + bytes(47)),
        ("zero", bytes(48)),
        ("x_is_p", bytes([P.to_bytes(48, "big")[0] | 0x80]) + P.to_bytes(48, "big")[1:]),
        ("x_above_p", bytes([(P + 1).to_bytes(48, "big")[0] | 0x80]) + (P + 1).to_bytes(48, "big")[1:]),
        ("x_all_ones", b"\x9f" + b"\xff" * 47),
    ]
    small = 5                                   # x + p fits below the flag bits for a small x
    xs = (small + P).to_bytes(48, "big")
    out.append(("x_plus_p", bytes([xs[0] | 0x80]) + xs[1:]))
    while len(out) < 14:
        x = rng.randrange(P)
        if fp_sqrt((x * x * x + 4) % P) is None:
            b = bytearray(fp_bytes(x))
            b[0] |= 0x80
            out.append((f"not_on_curve_{len(out)}", bytes(b)))
    return out


def bad_g2(rng):
    good = on_curve_g2(rng, True)
    pb = P.to_bytes(48, "big")
    out = [
        ("no_compression_flag", bytes([good[0] & 0x7F]) + good[1:]),
        ("infinity_and_sign", b"\xe0" + bytes(95)),
        ("infinity_with_x", b"\xc0" + bytes(94) + b"\x01"),
        ("zero", bytes(96)),
        ("x1_is_p", bytes([pb[0] | 0x80]) + pb[1:] + good[48:]),
        ("x0_is_p", good[:48] + pb),
        ("x_all_ones", b"\x9f" + b"\xff" * 95),
    ]
    while len(out) < 12:
        x = (rng.randrange(P), rng.randrange(P))
        rhs = f2_mul(f2_mul(x, x), x)
        if f2_sqrt(((rhs[0] + 4) % P, (rhs[1] + 4) % P)) is None:
            b = bytearray(fp_bytes(x[1]) + fp_bytes(x[0]))
            b[0] |= 0x80
            out.append((f"not_on_curve_{len(out)}", bytes(b)))
    return out


def write_generated():
    rng = random.Random(0x0B15)
    f = CaseFile("bls-generated.bin")
    edge = [1, 2, 3, R - 1, R - 2, (R - 1) // 2, (R + 1) // 2, 1 << 128, (1 << 254) + 1]
    keys = edge + [rng.randrange(1, R) for _ in range(20)]
    for k in keys:
        add_sk_to_pk(f, f"sk_to_pk_{k:x}", k.to_bytes(32, "big"))
    for k in (0, R, R + 1, (1 << 256) - 1):
        add_sk_to_pk(f, f"sk_to_pk_bad_{k:x}", k.to_bytes(32, "big"))
    lengths = [0, 1, 31, 32, 33, 55, 56, 63, 64, 65, 100, 128, 200, 255, 256, 1000]
    pairs = []
    for n, k in enumerate(keys[:16]):
        msg = bytes(rng.randrange(256) for _ in range(lengths[n]))
        sig = add_sign(f, f"sign_{n}", k.to_bytes(32, "big"), msg)
        pairs.append((sk_to_pk(k), msg, sig, k))
    for k in (0, R, (1 << 256) - 1):
        add_sign(f, f"sign_bad_{k:x}", k.to_bytes(32, "big"), b"abc")
    for n, (pk, msg, sig, k) in enumerate(pairs):
        add_verify(f, f"verify_{n}", pk, msg, sig)
        add_verify(f, f"verify_wrong_message_{n}", pk, msg + b"\x00", sig)
        other = pairs[(n + 1) % len(pairs)]
        add_verify(f, f"verify_wrong_key_{n}", other[0], msg, sig)
        flipped = bytearray(sig)
        flipped[95] ^= 1
        add_verify(f, f"verify_flipped_{n}", pk, msg, bytes(flipped))
    pk, msg, sig, _ = pairs[3]
    add_verify(f, "verify_infinity_key", G1_INF, msg, sig)
    add_verify(f, "verify_infinity_signature", pk, msg, G2_INF)
    add_verify(f, "verify_key_off_subgroup", on_curve_g1(rng, False), msg, sig)
    add_verify(f, "verify_signature_off_subgroup", pk, msg, on_curve_g2(rng, False))
    for name, b in bad_g1(rng)[:6]:
        add_verify(f, f"verify_key_{name}", b, msg, sig)
    for name, b in bad_g2(rng)[:6]:
        add_verify(f, f"verify_signature_{name}", pk, msg, b)
    # Aggregation over one message.
    msg = b"\x5a" * 32
    signers = keys[:12]
    sigs = [sign(k, msg) for k in signers]
    pks = [sk_to_pk(k) for k in signers]
    for n in (1, 2, 3, 5, 12):
        st, agg = add_aggregate(f, f"aggregate_{n}", sigs[:n])
        add_fast(f, f"fast_{n}", pks[:n], msg, agg)
        add_eth_fast(f, f"eth_fast_{n}", pks[:n], msg, agg)
        add_fast(f, f"fast_missing_key_{n}", pks[:n - 1] + pks[n:n + 1], msg, agg)
        add_eth_aggregate(f, f"eth_aggregate_{n}", pks[:n])
    add_aggregate(f, "aggregate_empty", [])
    add_aggregate(f, "aggregate_infinity", [G2_INF, sigs[0]])
    add_aggregate(f, "aggregate_off_subgroup", [sigs[0], on_curve_g2(rng, False)])
    for name, b in bad_g2(rng)[:6]:
        add_aggregate(f, f"aggregate_{name}", [sigs[0], b])
    add_fast(f, "fast_empty", [], msg, G2_INF)
    add_eth_fast(f, "eth_fast_empty_infinity", [], msg, G2_INF)
    add_eth_fast(f, "eth_fast_empty_other", [], msg, sigs[0])
    neg = bytes((-ark_g1(pks[0])).to_compressed_bytes())
    add_fast(f, "fast_cancelling_keys", [pks[0], neg], msg, G2_INF)
    st, twice = aggregate([sigs[0], sigs[0], sigs[1]])
    add_fast(f, "fast_repeated_key", [pks[0], pks[0], pks[1]], msg, twice)
    add_fast(f, "fast_repeated_key_once", [pks[0], pks[1]], msg, twice)
    add_eth_aggregate(f, "eth_aggregate_cancelling_keys", [pks[0], neg])
    add_eth_aggregate(f, "eth_aggregate_empty", [])
    add_eth_aggregate(f, "eth_aggregate_infinity", [pks[0], G1_INF])
    add_eth_aggregate(f, "eth_aggregate_off_subgroup", [pks[0], on_curve_g1(rng, False)])
    for name, b in bad_g1(rng)[:6]:
        add_eth_aggregate(f, f"eth_aggregate_{name}", [pks[0], b])
        add_fast(f, f"fast_{name}", [pks[0], b], msg, sigs[0])
    # Keys and points.
    for n in range(10):
        add_key_validate(f, f"key_validate_{n}", pks[n])
    add_key_validate(f, "key_validate_infinity", G1_INF)
    for n in range(4):
        add_key_validate(f, f"key_validate_off_subgroup_{n}", on_curve_g1(rng, False))
    for name, b in bad_g1(rng):
        add_key_validate(f, f"key_validate_{name}", b)
        add_g1_decode(f, f"g1_decode_{name}", b)
    for name, b in bad_g2(rng):
        add_g2_decode(f, f"g2_decode_{name}", b)
    add_g1_decode(f, "g1_decode_infinity", G1_INF)
    add_g2_decode(f, "g2_decode_infinity", G2_INF)
    for n in range(8):
        add_g1_decode(f, f"g1_decode_{n}", on_curve_g1(rng, True))
        add_g1_decode(f, f"g1_decode_off_subgroup_{n}", on_curve_g1(rng, False))
        add_g2_decode(f, f"g2_decode_{n}", on_curve_g2(rng, True))
        add_g2_decode(f, f"g2_decode_off_subgroup_{n}", on_curve_g2(rng, False))
    points = [on_curve_g1(rng, True) for _ in range(10)] + [G1_INF]
    for n in range(len(points)):
        a, b = points[n], points[(n + 3) % len(points)]
        s = bytes((ark_g1(a) + ark_g1(b)).to_compressed_bytes())
        f.add(K_G1_ADD, f"g1_add_{n}", a, b, s)
        f.add(K_G1_NEG, f"g1_neg_{n}", a, bytes((-ark_g1(a)).to_compressed_bytes()))
    a = points[0]
    na = bytes((-ark_g1(a)).to_compressed_bytes())
    f.add(K_G1_ADD, "g1_add_double", a, a, bytes((ark_g1(a) + ark_g1(a)).to_compressed_bytes()))
    f.add(K_G1_ADD, "g1_add_opposite", a, na, G1_INF)
    f.add(K_G1_ADD, "g1_add_infinity", G1_INF, G1_INF, G1_INF)
    # Hashing.
    dsts = [b"", b"D", DST, QUUX, b"x" * 255, b"y" * 256, b"z" * 300]
    for n, dst in enumerate(dsts):
        for length in (0, 1, 32, 33, 64, 255, 256, 257, 8160, 8161):
            msg = bytes(rng.randrange(256) for _ in range(rng.choice([0, 1, 32, 64, 65, 200])))
            add_xmd(f, f"xmd_{n}_{length}", msg, dst, length)
        add_xmd(f, f"xmd_{n}_65535", b"m", dst, 65535)
    for n in range(12):
        msg = bytes(rng.randrange(256) for _ in range(lengths[n]))
        add_hash_to_g2(f, f"hash_to_g2_{n}", msg, dsts[n % len(dsts)])
    f.write()


if __name__ == "__main__":                 # kzg.py loads the helpers above without this part
    write_official()
    write_generated()
    with open(os.path.join(out_dir, "manifest-bls.txt"), "w") as fh:
        fh.write("\n".join(manifest) + "\n")
