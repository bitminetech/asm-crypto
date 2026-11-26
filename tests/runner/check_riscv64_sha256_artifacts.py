#!/usr/bin/env python3
"""Compare the Linux RV64GC linked SHA-256 image with the Lean fixture."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_arm64_artifacts import archive_object, chunk, require, unpack
from check_x86_sha256_artifacts import archive_binding

ROOT = Path(__file__).resolve().parents[2]
SYMBOL = "crypto_sha256"
CODE_BYTES = 0x416
IMAGE_BYTES = 0x540


def symbol_image(executable, nm):
    symbols = subprocess.check_output([nm, "-S", "--defined-only", executable], text=True)
    definitions = [fields for line in symbols.splitlines()
                   if (fields := line.split()) and fields[-1] == SYMBOL]
    require(len(definitions) == 1 and len(definitions[0]) == 4, "expected one SHA-256 symbol")
    address, size, kind, _ = definitions[0]
    address = int(address, 16)
    require(kind == "T" and int(size, 16) == CODE_BYTES and address % 16 == 0,
            "unexpected SHA-256 symbol type, size or alignment")

    data = executable.read_bytes()
    require(data[:7] == b"\x7fELF\x02\x01\x01", "expected little-endian ELF64")
    require(unpack("<HH", data, 16) == (2, 243), "expected a RISC-V ELF executable")
    table, = unpack("<Q", data, 32)
    stride, count = unpack("<HH", data, 54)
    require(stride == 56 and count != 0, "invalid ELF program header table")
    images = []
    for i in range(count):
        kind, flags, offset, vaddr, _, file_size, mem_size, _ = unpack(
            "<IIQQQQQQ", data, table + i * stride)
        if kind != 1 or not vaddr <= address < vaddr + mem_size:
            continue
        require(flags == 5, "expected an executable, readable, non-writable segment")
        require(file_size <= mem_size and address + IMAGE_BYTES <= vaddr + file_size,
                "SHA-256 image exceeds the file-backed segment")
        images.append(chunk(data, offset + address - vaddr, IMAGE_BYTES))
    require(len(images) == 1, "SHA-256 image must be backed by one load segment")
    return images[0]


def model_image(root):
    source = (root / "lean/Models/RISCV64SHA256Image.lean").read_text()
    fixture = re.search(r"^def image : Array UInt8 := #\[([\s\S]*?)^\]", source, re.MULTILINE)
    require(fixture is not None, "missing Lean image")
    values = [value.strip() for value in fixture[1].split(",")]
    require(all(re.fullmatch(r"0x[0-9a-f]{2}", value) for value in values), "invalid Lean image bytes")
    return bytes(int(value, 16) for value in values)


def check(build, lld="ld.lld", nm="llvm-nm", root=ROOT):
    directory = build / "linux-riscv64"
    archive_path = directory / "libasm-crypto.a"
    archive = archive_path.read_bytes()
    obj = archive_object(archive)
    require(obj == (directory / "sha256.o").read_bytes(), "object/archive mismatch")
    location = archive_binding("linux", archive, obj, SYMBOL.encode("ascii"))
    expected = model_image(root)
    with tempfile.TemporaryDirectory() as temp:
        linked = Path(temp) / "sha256"
        subprocess.run([lld, "-m", "elf64lriscv", "-e", SYMBOL, "-u", SYMBOL,
                        "-o", linked, archive_path], check=True)
        require(symbol_image(linked, nm) == expected, "linked archive image differs from Lean")
    require(symbol_image(directory / "runner", nm) == expected, "runner image differs from Lean")
    return {"target": "linux-riscv64", "symbol": SYMBOL, "archive_member_offset": location,
            "function_bytes": CODE_BYTES, "image_bytes": len(expected),
            "object_sha256": hashlib.sha256(obj).hexdigest(),
            "image_sha256": hashlib.sha256(expected).hexdigest()}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, default=ROOT / "build")
    parser.add_argument("--lld", default="ld.lld")
    parser.add_argument("--nm", default="llvm-nm")
    args = parser.parse_args()
    print(json.dumps(check(args.build, args.lld, args.nm), indent=2))
