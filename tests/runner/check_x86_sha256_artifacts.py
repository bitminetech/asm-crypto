#!/usr/bin/env python3
"""Check the scalar x86 SHA-256 proof image against relocatable archive members."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_arm64_artifacts import archive_object, chunk, require

ROOT = Path(__file__).resolve().parents[2]
# Whole-object identities fix the symbol, text bounds, relocations and metadata
# inspected with llvm-readobj on the pinned toolchain. Offsets below are valid
# only for these exact objects. The entry is at byte zero of each text section.
OBJECTS = {
    "linux": ("00122dee958bdfbd2d2a418721a943ecb3aeb1420d0f4e248c0f17c6b56f7dad", 64),
    "macos": ("f7fb241caaab86bd236cce79b3c53d077137fa25cacf64c4d5db43bb94bcfe1a", 472),
    "windows": ("00e70ba8cfe1f9545657d172f7b29bcf014d499ff4b911763ad8bbc3bb1a13d7", 220),
}


def image_source(text):
    rows = [", ".join(f"0x{v:02x}" for v in text[i:i + 16]) for i in range(0, len(text), 16)]
    return ("import Init.Data.BitVec.Basic\n\nnamespace Crypto.X86_64\n\n"
            "/-- Baseline text image including alignment bytes, K and the IV.\n"
            "Compared to the three archive members by check_x86_sha256_artifacts.py. -/\n"
            "def image : Array UInt8 := #[\n  " + ",\n  ".join(rows) +
            "\n]\n\nend Crypto.X86_64\n")


def table_int(table, offset, size, order):
    return int.from_bytes(chunk(table, offset, size), order)


def indexed_symbol(names, count, symbol, *, ordered=False):
    entries = names.split(b"\0")
    require(len(entries) > count and not any(entries[count:]), "invalid archive symbol names")
    entries = entries[:count]
    require(all(entries), "empty archive symbol name")
    require(not ordered or entries == sorted(entries), "unsorted archive symbol directory")
    indices = [i for i, name in enumerate(entries) if name == symbol]
    require(len(indices) == 1, "archive symbol must occur exactly once")
    return indices[0]


def archive_member(data, offset):
    header = chunk(data, offset, 60)
    require(header[58:] == b"`\n", "invalid archive header")
    size = int(header[48:58])
    member = chunk(data, offset + 60, size)
    name = header[:16].decode("ascii").strip()
    if name.startswith("#1/"):
        name_bytes = int(name[3:])
        name = chunk(member, 0, name_bytes).rstrip(b"\0").decode("ascii")
        member = member[name_bytes:]
    return name, member, offset + 60 + size + size % 2


def archive_binding(target, archive, member, symbol):
    """Resolve the symbol using each linker directory shipped for this OS."""
    name, table, following = archive_member(archive, 8)
    if target == "macos":
        require(name in ("__.SYMDEF", "__.SYMDEF SORTED"), "missing Darwin archive symbol directory")
        size = table_int(table, 0, 4, "little")
        require(size % 8 == 0, "invalid Darwin ranlib table")
        records = chunk(table, 4, size)
        names = chunk(table, 8 + size, table_int(table, 4 + size, 4, "little"))
        matches = []
        previous = b""
        for offset in range(0, size, 8):
            index = table_int(records, offset, 4, "little")
            require(index < len(names) and (index == 0 or names[index - 1] == 0), "invalid ranlib name offset")
            end = names.find(b"\0", index)
            require(end >= 0, "unterminated ranlib name")
            entry = names[index:end]
            require(name != "__.SYMDEF SORTED" or previous <= entry, "unsorted archive symbol directory")
            previous = entry
            if entry == symbol:
                matches.append(table_int(records, offset + 4, 4, "little"))
        require(len(matches) == 1, "archive symbol must occur exactly once")
        location = matches[0]
    else:
        require(name == "/", "missing archive symbol directory")
        count = table_int(table, 0, 4, "big")
        offsets = chunk(table, 4, 4 * count)
        index = indexed_symbol(table[4 + len(offsets):], count, symbol)
        location = table_int(offsets, 4 * index, 4, "big")
        if target == "windows":
            name, second, _ = archive_member(archive, following)
            require(name == "/", "missing COFF second linker member")
            objects = table_int(second, 0, 4, "little")
            offsets = chunk(second, 4, 4 * objects)
            count = table_int(second, 4 + len(offsets), 4, "little")
            indices = chunk(second, 8 + len(offsets), 2 * count)
            index = indexed_symbol(second[8 + len(offsets) + len(indices):], count, symbol, ordered=True)
            ordinal = table_int(indices, 2 * index, 2, "little")
            require(1 <= ordinal <= objects and table_int(offsets, 4 * (ordinal - 1), 4, "little") == location,
                    "COFF archive symbol directories disagree")
    name, resolved, _ = archive_member(archive, location)
    require(name.rstrip("/") == "sha256.o" and resolved == member, "archive symbol resolves to a different object")
    return location


def check_target(target, archive, standalone, model):
    identity, offset = OBJECTS[target]
    member = archive_object(archive)
    require(member == standalone, target + ": object/archive mismatch")
    require(hashlib.sha256(member).hexdigest() == identity, target + ": unexpected object identity")
    text = member[offset:offset + 1200]
    require(image_source(text) == model, target + ": Lean image mismatch")
    symbol = "_crypto_sha256" if target == "macos" else "crypto_sha256"
    location = archive_binding(target, archive, member, symbol.encode("ascii"))
    return {"target": target + "-x86_64", "symbol": symbol, "archive_member_offset": location,
            "entry_offset": 0, "function_bytes": 901, "text_bytes": len(text),
            "object_sha256": identity, "archive_sha256": hashlib.sha256(archive).hexdigest(),
            "text_sha256": hashlib.sha256(text).hexdigest()}


def check(build, root=ROOT):
    model = (root / "lean/Models/X86SHA256Image.lean").read_text()
    reports = []
    for target in OBJECTS:
        folder = build / (target + "-x86_64")
        reports.append(check_target(target, (folder / "libasm-crypto.a").read_bytes(),
                                    (folder / "sha256.o").read_bytes(), model))
    return reports


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, default=ROOT / "build")
    print(json.dumps(check(parser.parse_args().build), indent=2))
