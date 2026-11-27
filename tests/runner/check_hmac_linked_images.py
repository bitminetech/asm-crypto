#!/usr/bin/env python3
"""Match linked HMAC entry points and both helpers to their Lean images."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_arm64_artifacts import chunk, require, unpack
from check_riscv64_sha256_artifacts import CODE_BYTES as RISCV_SHA_CODE_BYTES
from check_riscv64_sha256_artifacts import IMAGE_BYTES as RISCV_SHA_IMAGE_BYTES
from check_riscv64_sha256_artifacts import model_image as riscv_sha256_image
from check_x86_sha256_artifacts import image_source as x86_sha256_source

ROOT = Path(__file__).resolve().parents[2]
IMAGE = "lean/Models/HMACSHA256Image.lean"
TARGETS = {
    "arm64": ("ARM64", 183, 604, 896),
    "x86_64": ("X86_64", 62, 901, 1200),
    "riscv64": ("RISCV64", 243, RISCV_SHA_CODE_BYTES, RISCV_SHA_IMAGE_BYTES),
}
ROUTINES = {
    "entry": ("crypto_hmac_sha256", "T"),
    "key": ("crypto_hmac_key", "t"),
    "finish": ("crypto_hmac_finish", "t"),
    "sha256": ("crypto_sha256", "T"),
}


def read_images(executable, nm, machine, sha_code_size, sha_image_size):
    data = executable.read_bytes()
    require(data[:7] == b"\x7fELF\x02\x01\x01", "expected little-endian ELF64")
    require(unpack("<HH", data, 16) == (2, machine), "unexpected ELF target or type")
    table, = unpack("<Q", data, 32)
    stride, count = unpack("<HH", data, 54)
    require(stride == 56 and count > 0, "invalid ELF program header table")
    loads = []
    for i in range(count):
        kind, flags, offset, address, _, file_size, mem_size, _ = unpack(
            "<IIQQQQQQ", data, table + stride * i)
        require(kind not in (2, 3), "the modeled runner must have a static ELF load map")
        if kind == 1:
            require(file_size <= mem_size and offset + file_size <= len(data)
                    and address + mem_size <= 1 << 64, "invalid ELF load segment")
            loads.append((flags, offset, address, file_size, mem_size))

    symbols = subprocess.check_output([nm, "-S", "--defined-only", executable], text=True)
    rows = [line.split() for line in symbols.splitlines() if line.strip()]
    images = {}
    for name, (symbol, symbol_type) in ROUTINES.items():
        definitions = [row for row in rows if row[-1] == symbol]
        require(len(definitions) == 1 and len(definitions[0]) == 4, f"expected one {symbol}")
        address_hex, size_hex, kind, _ = definitions[0]
        address, size = int(address_hex, 16), int(size_hex, 16)
        require(kind == symbol_type and size > 0, f"unexpected type or size of {symbol}")
        if name == "sha256":
            require(size == sha_code_size and address % 16 == 0, "unexpected SHA-256 entry")
            size = sha_image_size
        end = address + size
        mappings = [(flags, offset, start, file_size)
                    for flags, offset, start, file_size, mem_size in loads
                    if start < end and address < start + mem_size]
        require(len(mappings) == 1, f"expected one load mapping for {symbol}")
        flags, offset, start, file_size = mappings[0]
        require(flags == 5 and start <= address and end <= start + file_size,
                f"unmapped executable {symbol}")
        images[name] = (address, chunk(data, offset + address - start, size))
    return images


def read_macos_images(executable, nm, target, expected):
    data = executable.read_bytes()
    magic, cpu, subtype, kind, count, command_bytes, _, _ = unpack("<8I", data, 0)
    target_header = {"arm64": (0x100000c, 0), "x86_64": (0x1000007, 3)}
    require(magic == 0xfeedfacf and kind == 2 and (cpu, subtype) == target_header[target],
            f"expected a {target} Mach-O executable")
    chunk(data, 32, command_bytes)
    cursor = 32
    mappings = []
    for _ in range(count):
        command, size = unpack("<II", data, cursor)
        require(size >= 8 and cursor + size <= 32 + command_bytes, "invalid Mach-O command")
        if command == 0x19:
            require(size >= 72, "invalid Mach-O segment")
            address, length, offset, file_size, max_prot, initial_prot = unpack(
                "<QQQQii", data, cursor + 24)
            require(file_size <= length and offset + file_size <= len(data)
                    and address + length <= 1 << 64, "invalid Mach-O load segment")
            mappings.append((address, length, offset, file_size, max_prot, initial_prot))
        cursor += size
    require(cursor == 32 + command_bytes, "invalid Mach-O command count")

    symbols = subprocess.check_output([nm, "-n", executable], text=True)
    rows = [line.split() for line in symbols.splitlines()]
    images = {}
    for name, (symbol, expected_kind) in ROUTINES.items():
        native_symbol = "_" + symbol if expected_kind == "T" else symbol
        definitions = [row for row in rows if row and row[-1] == native_symbol]
        require(len(definitions) == 1 and len(definitions[0]) == 3,
                f"expected one {native_symbol}")
        address_hex, kind, _ = definitions[0]
        address = int(address_hex, 16)
        require(kind == expected_kind and address % 4 == 0, f"invalid {native_symbol}")
        length = len(expected[name][1])
        end = address + length
        segments = [mapping for mapping in mappings
                    if mapping[0] < end and address < mapping[0] + mapping[1]]
        require(len(segments) == 1, f"expected one load mapping for {native_symbol}")
        start, _, offset, file_size, max_prot, initial_prot = segments[0]
        require(initial_prot == 5 and max_prot == 5 and start <= address
                and end <= start + file_size, f"unmapped executable {native_symbol}")
        images[name] = (address, chunk(data, offset + address - start, length))
    return images


def match_load_layout(actual, expected):
    actual_base = actual["entry"][0]
    expected_base = expected["entry"][0]
    for name, (address, code) in actual.items():
        expected_address, expected_code = expected[name]
        require(address - actual_base == expected_address - expected_base,
                f"unexpected displacement for {ROUTINES[name][0]}")
        require(code == expected_code, f"unexpected executable bytes for {ROUTINES[name][0]}")


def checked_images(build, nm, root):
    images = {}
    for target, (_, machine, sha_code_size, sha_image_size) in TARGETS.items():
        executable = build / f"linux-{target}" / "runner"
        routines = read_images(executable, nm, machine, sha_code_size, sha_image_size)
        sha256 = routines["sha256"][1]
        if target == "arm64":
            expected = bytes.fromhex((root / "lean/Models/arm64-sha256.text.hex").read_text())
            require(sha256 == expected, "linked ARM64 SHA-256 image differs from the proof image")
        elif target == "x86_64":
            expected = (root / "lean/Models/X86SHA256Image.lean").read_text()
            require(x86_sha256_source(sha256) == expected,
                    "linked x86-64 SHA-256 image differs from the proof image")
        else:
            require(sha256 == riscv_sha256_image(root),
                    "linked RV64 SHA-256 image differs from the proof image")
        images[target] = routines
    return images


def render_image(images):
    parts = [
        "import Init.Data.BitVec.Basic\n",
        "/-! Linux runner code for the HMAC entry and its two local helpers.",
        "The offsets are relative to the HMAC entry. Checked by check_hmac_linked_images.py. -/\n",
        "namespace Crypto.HMACSHA256\n",
        "structure Routine where",
        "  offset : Int",
        "  image : Array UInt8\n",
    ]
    for target, (namespace, *_) in TARGETS.items():
        routines = images[target]
        base = routines["entry"][0]
        parts.extend((f"namespace {namespace}\n",
                      f"def sha256Offset : Int := {routines['sha256'][0] - base}\n"))
        for name in ("entry", "key", "finish"):
            address, code = routines[name]
            rows = [", ".join(f"0x{byte:02x}" for byte in code[i:i + 16])
                    for i in range(0, len(code), 16)]
            parts.append(f"def {name} : Routine := ⟨{address - base}, #[\n  "
                         + ",\n  ".join(rows) + "\n]⟩\n")
        parts.append(f"end {namespace}\n")
    parts.append("end Crypto.HMACSHA256\n")
    return "\n".join(parts)


def check(build, nm, root, macos_arm64=None, macos_x86_64=None):
    images = checked_images(build, nm, root)
    require(render_image(images) == (root / IMAGE).read_text(),
            "linked HMAC routine bytes or load offsets differ from the Lean image")
    linked = {f"linux-{target}": routines for target, routines in images.items()}
    for target, executable in (("arm64", macos_arm64), ("x86_64", macos_x86_64)):
        if executable is not None:
            actual = read_macos_images(executable, nm, target, images[target])
            match_load_layout(actual, images[target])
            linked[f"macos-{target}"] = actual
    records = {}
    for target, routines in linked.items():
        executable = build / target / "runner" if target.startswith("linux-") else (
            macos_arm64 if target == "macos-arm64" else macos_x86_64)
        base = routines["entry"][0]
        records[target] = {
            "filename": "runner",
            "sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
            "entry_address": base,
            "routines": {
                ROUTINES[name][0]: {"offset": addr - base, "bytes": len(code),
                                    "sha256": hashlib.sha256(code).hexdigest()}
                for name, (addr, code) in routines.items()
            },
        }
    return records


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, default=ROOT / "build")
    parser.add_argument("--nm", default="llvm-nm")
    parser.add_argument("--macos-arm64", type=Path, metavar="RUNNER")
    parser.add_argument("--macos-x86-64", type=Path, metavar="RUNNER")
    args = parser.parse_args()
    print(json.dumps(check(args.build, args.nm, ROOT, args.macos_arm64, args.macos_x86_64), indent=2))
