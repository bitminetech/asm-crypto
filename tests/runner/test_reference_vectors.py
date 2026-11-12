#!/usr/bin/env python3
"""Validate official vector coverage and exercise the streaming test adapter.

Fixture expectations come independently from Python hashlib.sha256. Inputs are
deterministic: all power-of-two periods from 1 to 64 and five aligned lengths.
Generated vectors stay in the ignored build directory.
"""
import hashlib
from pathlib import Path
import struct
import subprocess
import sys

OFFICIAL = {
    "acvp-aft.bin": "9c0e0dc2ca33ca379eb0657ab263ce45302483313952c862b3bc51e9470f8d7b",
    "acvp-mct.bin": "508ed019097025e309d83232094b519849a994b695e1d7b0866874b329672c3b",
    "acvp-ldt.bin": "8ece77fc197477e8140d86df51b0e79d561b587eb0693927ddc729ba974cb6d4",
    "cavp-short.bin": "741301e4e5707071d2eb5f195523f303426d54d2a78931fa5f25426cfcac50a0",
    "cavp-long.bin": "303349299a2ec10062f6e19d3bcfcc118d5924db99a01782bf4ba68118b3d8f0",
    "cavp-monte.bin": "953bb94904baa7129a985942bdc88c18c7b1af48223a75dfb462f70093d679c6",
    "boundary.bin": "c6c7c609b3d906d9f2111fb7ea7db19a7ea4b09f436f29d930bb1e203860a252",
}


def u64(value):
    return struct.pack("<Q", value)


def case(pattern, length):
    message = (pattern * ((length + len(pattern) - 1) // len(pattern)))[:length]
    return u64(len(pattern)) + pattern + u64(length) + hashlib.sha256(message).digest()


def main():
    root = Path(__file__).resolve().parents[2]
    vectors = Path(sys.argv[1])
    for name, expected in OFFICIAL.items():
        actual = hashlib.sha256((vectors / name).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(name + ": vector coverage/content differs from the recorded generator output")
    print("All seven official vector files have the recorded checksums")
    output = root / "build/verification/reference-fixtures"
    output.mkdir(parents=True, exist_ok=True)
    cases = [case(bytes((i * 17 + 3) % 256 for i in range(period)), length)
             for period in (1, 2, 4, 8, 16, 32, 64) for length in (0, 64, 128, 192, 4096)]
    valid = b"SHA256V1" + u64(3) + u64(len(cases)) + b"".join(cases)
    fixtures = (
        ("aligned-periods", valid, 0, "35 reference checks passed"),
        ("wrong-digest", valid[:-1] + bytes([valid[-1] ^ 1]), 1, "failed"),
        ("unsupported-period", b"SHA256V1" + u64(3) + u64(1) + case(b"abc", 64),
         1, "outside the proved"),
        ("truncated", valid[:-1], 1, "truncated"),
    )
    for name, data, expected_exit, expected_message in fixtures:
        path = output / (name + ".bin")
        path.write_bytes(data)
        result = subprocess.run([str(root / ".lake/build/bin/reference-vectors"), str(path)],
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if result.returncode != expected_exit or expected_message not in result.stdout:
            raise RuntimeError(name + ": unexpected runner behavior\n" + result.stdout)
        print(name + ": expected result")


if __name__ == "__main__":
    main()
