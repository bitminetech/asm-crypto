#!/usr/bin/env python3
"""Fetch, check and convert the SHA-256 test vectors into binary case files.

Usage: python3 -I tests/generator/generate.py OUT_DIR

OUT_DIR must be outside this repo. The format of the files is in README.md
next to this script. The script uses only the Python standard library.
"""
import hashlib
import io
import json
import pathlib
import struct
import sys
import urllib.request
import zipfile

ACVP_URL = (
    "https://raw.githubusercontent.com/usnistgov/ACVP-Server/"
    "975de31eb83d87039ec88934fdc47d8c312b892d/"
    "gen-val/json-files/SHA2-256-1.0/internalProjection.json"
)
ACVP_SHA256 = "a7e0bf4f5c661f1787b343bf3ae1a809b1e62f8fb2c8a627791510d03a570a6c"
CAVP_URL = (
    "https://csrc.nist.gov/CSRC/media/Projects/"
    "Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip"
)
CAVP_SHA256 = "929ef80b7b3418aca026643f6f248815913b60e01741a44bba9e118067f4c9b8"

MAGIC = b"SHA256V1"
KIND_MESSAGE = 1
KIND_MONTE = 2
KIND_LARGE = 3
MONTE_CAVP = 1
MONTE_ACVP_ALTERNATE = 2
BOUNDARY_MAX = 512


def fail(text):
    sys.exit("generate.py: " + text)


def u64(n):
    return struct.pack("<Q", n)


def fetch(url, sha256, cache):
    """Return the bytes at url, from cache when present, after the pin check."""
    path = cache / url.rsplit("/", 1)[1]
    if path.exists():
        data = path.read_bytes()
    else:
        # The NIST site refuses the default Python client name.
        request = urllib.request.Request(url, headers={"User-Agent": "asm-crypto-vector-generator"})
        with urllib.request.urlopen(request) as response:
            data = response.read()
        path.write_bytes(data)
    got = hashlib.sha256(data).hexdigest()
    if got != sha256:
        fail(f"{url} has SHA-256 {got}, expected {sha256}")
    return data


def write(out, name, kind, cases):
    body = b"".join(cases)
    data = MAGIC + u64(kind) + u64(len(cases)) + body
    (out / name).write_bytes(data)
    return name, len(cases), hashlib.sha256(data).hexdigest()


def message_case(msg, md):
    if len(md) != 32:
        fail("a digest is not 32 bytes")
    return u64(len(msg)) + msg + md


def monte_case(variant, seed, mds):
    return u64(variant) + u64(len(seed)) + seed + u64(len(mds)) + b"".join(mds)


def large_case(content, full_length, md):
    return u64(len(content)) + content + u64(full_length) + md


def bits_to_bytes(bits):
    if bits % 8:
        fail(f"length {bits} bits is not a whole number of bytes")
    return bits // 8


def acvp(data):
    doc = json.loads(data)
    if doc.get("algorithm") != "SHA2-256" or doc.get("revision") != "1.0":
        fail("the ACVP file is not SHA2-256 revision 1.0")
    aft, mct, ldt = [], [], []
    for group in doc["testGroups"]:
        kind = group["testType"]
        for test in group["tests"]:
            if kind == "AFT":
                msg = bytes.fromhex(test["msg"])
                if len(msg) != bits_to_bytes(test["len"]):
                    fail(f"ACVP case {test['tcId']} has a wrong length")
                aft.append(message_case(msg, bytes.fromhex(test["md"])))
            elif kind == "MCT":
                if group["mctVersion"] != "alternate":
                    fail(f"ACVP MCT version {group['mctVersion']} is not supported")
                seed = bytes.fromhex(test["msg"])
                if len(seed) != bits_to_bytes(test["len"]):
                    fail(f"ACVP case {test['tcId']} has a wrong seed length")
                mds = [bytes.fromhex(r["md"]) for r in test["resultsArray"]]
                mct.append(monte_case(MONTE_ACVP_ALTERNATE, seed, mds))
            elif kind == "LDT":
                large = test["largeMsg"]
                if large["expansionTechnique"] != "repeating":
                    fail(f"ACVP LDT expansion {large['expansionTechnique']} is not supported")
                content = bytes.fromhex(large["content"])
                if len(content) != bits_to_bytes(large["contentLength"]):
                    fail(f"ACVP case {test['tcId']} has a wrong content length")
                full = bits_to_bytes(large["fullLength"])
                ldt.append(large_case(content, full, bytes.fromhex(test["md"])))
            else:
                fail(f"ACVP test type {kind} is not supported")
    return aft, mct, ldt


def rsp_pairs(text):
    for line in text.splitlines():
        line = line.strip()
        if " = " in line and not line.startswith("#"):
            key, value = line.split(" = ", 1)
            yield key, value


def cavp_messages(text):
    cases, length, msg = [], None, None
    for key, value in rsp_pairs(text):
        if key == "Len":
            length = bits_to_bytes(int(value))
        elif key == "Msg":
            msg = bytes.fromhex(value)[:length]
            if len(msg) != length:
                fail("a CAVP message is shorter than its length")
        elif key == "MD":
            cases.append(message_case(msg, bytes.fromhex(value)))
    return cases


def cavp_monte(text):
    seed, mds = None, []
    for key, value in rsp_pairs(text):
        if key == "Seed":
            seed = bytes.fromhex(value)
        elif key == "MD":
            mds.append(bytes.fromhex(value))
    if seed is None or len(mds) != 100:
        fail("the CAVP Monte file does not hold one seed and 100 digests")
    return [monte_case(MONTE_CAVP, seed, mds)]


def cavp(data):
    names = {
        "short": "shabytetestvectors/SHA256ShortMsg.rsp",
        "long": "shabytetestvectors/SHA256LongMsg.rsp",
        "monte": "shabytetestvectors/SHA256Monte.rsp",
    }
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        text = {k: archive.read(v).decode("ascii") for k, v in names.items()}
    return cavp_messages(text["short"]), cavp_messages(text["long"]), cavp_monte(text["monte"])


def boundary():
    cases = []
    for length in range(BOUNDARY_MAX + 1):
        msg = bytes((i * 31 + 7) & 0xFF for i in range(length))
        cases.append(message_case(msg, hashlib.sha256(msg).digest()))
    return cases


def main():
    if len(sys.argv) != 2:
        fail("usage: python3 -I tests/generator/generate.py OUT_DIR")
    repo = pathlib.Path(__file__).resolve().parents[2]
    out = pathlib.Path(sys.argv[1]).resolve()
    if out == repo or repo in out.parents:
        fail(f"{out} is inside the repo; generated vectors are stored outside it")
    cache = out / "sources"
    cache.mkdir(parents=True, exist_ok=True)

    aft, mct, ldt = acvp(fetch(ACVP_URL, ACVP_SHA256, cache))
    short, long_, monte = cavp(fetch(CAVP_URL, CAVP_SHA256, cache))
    written = [
        write(out, "acvp-aft.bin", KIND_MESSAGE, aft),
        write(out, "acvp-mct.bin", KIND_MONTE, mct),
        write(out, "acvp-ldt.bin", KIND_LARGE, ldt),
        write(out, "cavp-short.bin", KIND_MESSAGE, short),
        write(out, "cavp-long.bin", KIND_MESSAGE, long_),
        write(out, "cavp-monte.bin", KIND_MONTE, monte),
        write(out, "boundary.bin", KIND_MESSAGE, boundary()),
    ]
    lines = [f"{name} {count} {digest}" for name, count, digest in written]
    (out / "manifest.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
