#!/usr/bin/env python3
"""Compare ARM64 objects/archives with the recorded program, without disassembly.

This is an artifact identity check, not a proof of the program's behavior.
The extraction/parsing code is trusted until its correspondence is proved.
"""
import argparse
import hashlib
import json
from pathlib import Path
import struct


def require(condition, message):
    if not condition:
        raise ValueError(message)


def chunk(data, start, length):
    require(0 <= start <= len(data) and 0 <= length <= len(data) - start,
            "out-of-file range")
    return data[start:start + length]


def unpack(fmt, data, offset):
    return struct.unpack(fmt, chunk(data, offset, struct.calcsize(fmt)))


def cstring(data, offset):
    require(0 <= offset < len(data), "invalid string offset")
    end = data.find(b"\0", offset)
    require(end >= 0, "unterminated string")
    return data[offset:end].decode("ascii")


def elf(data):
    require(data[:7] == b"\x7fELF\x02\x01\x01", "expected little-endian ELF64")
    kind, machine = unpack("<HH", data, 16)
    require((kind, machine) == (1, 183), "expected AArch64 relocatable ELF")
    table, = unpack("<Q", data, 40)
    stride, count, names_index = unpack("<HHH", data, 58)
    require(stride == 64 and 0 < names_index < count, "invalid ELF section table")
    sections = [unpack("<IIQQQQIIQQ", data, table + i * stride) for i in range(count)]
    names = chunk(data, sections[names_index][4], sections[names_index][5])
    executable = [(i, s) for i, s in enumerate(sections) if s[2] & 4 and s[5]]
    require(len(executable) == 1, "expected exactly one executable ELF section")
    index, text = executable[0]
    require(cstring(names, text[0]) == ".text" and text[3] == 0, "unexpected ELF text")
    for s in sections:
        require(not (s[1] in (4, 9) and s[7] == index and s[5]), "text relocations")
    exports = []
    for s in sections:
        if s[1] != 2:
            continue
        require(s[9] == 24 and s[5] % 24 == 0 and s[6] < count, "invalid ELF symbols")
        strings = sections[s[6]]
        strings = chunk(data, strings[4], strings[5])
        for offset in range(s[4], s[4] + s[5], 24):
            name, info, _, section, value, size = unpack("<IBBHQQ", data, offset)
            if info >> 4 in (1, 2) and section != 0:
                exports.append((cstring(strings, name), section, value, size, info & 15))
    require(exports == [("crypto_sha256", index, 0, 604, 2)], "unexpected ELF exports")
    return chunk(data, text[4], text[5])


def macho(data):
    magic, cpu, _, kind, ncommands, command_bytes, _, _ = unpack("<8I", data, 0)
    require((magic, cpu, kind) == (0xfeedfacf, 0x100000c, 1), "expected ARM64 Mach-O object")
    end = 32 + command_bytes
    chunk(data, 32, command_bytes)
    offset, section_index = 32, 0
    texts, exports = [], []
    for _ in range(ncommands):
        cmd, length = unpack("<II", data, offset)
        require(length >= 8 and offset + length <= end, "invalid Mach-O load command")
        if cmd == 0x19:  # LC_SEGMENT_64
            nsections, = unpack("<I", data, offset + 64)
            require(length == 72 + 80 * nsections, "invalid Mach-O segment")
            for j in range(nsections):
                s = unpack("<16s16sQQ8I", data, offset + 72 + j * 80)
                section_index += 1
                if s[8] & 0x80000400 and s[3]:
                    require(s[0].rstrip(b"\0") == b"__text" and s[1].rstrip(b"\0") == b"__TEXT",
                            "unexpected executable Mach-O section")
                    require(s[2] == 0 and s[7] == 0, "Mach-O text address/relocations")
                    texts.append((section_index, chunk(data, s[4], s[3])))
        elif cmd == 2:  # LC_SYMTAB
            symbol_offset, nsymbols, string_offset, string_bytes = unpack("<4I", data, offset + 8)
            strings = chunk(data, string_offset, string_bytes)
            for i in range(nsymbols):
                name, kind_bits, section, _, value = unpack("<IBBHQ", data, symbol_offset + 16 * i)
                if kind_bits & 1 and kind_bits & 0x0e != 0:
                    exports.append((cstring(strings, name), section, value, kind_bits & 0x0e))
        offset += length
    require(offset == end and len(texts) == 1, "unexpected Mach-O section/command count")
    require(exports == [("_crypto_sha256", texts[0][0], 0, 0x0e)], "unexpected Mach-O exports")
    return texts[0][1]


def coff(data):
    machine, count, _, symbols, nsymbols, optional_bytes, _ = unpack("<HHIIIHH", data, 0)
    require(machine == 0xaa64 and optional_bytes == 0, "expected ARM64 COFF object")
    texts = []
    for i in range(count):
        s = unpack("<8s6I2HI", data, 20 + 40 * i)
        if s[9] & 0x20000000 and s[3]:
            require(s[0].rstrip(b"\0") == b".text" and s[7] == 0,
                    "unexpected COFF executable section/relocations")
            texts.append((i + 1, chunk(data, s[4], s[3])))
    strings_at = symbols + 18 * nsymbols
    string_size, = unpack("<I", data, strings_at)
    strings = chunk(data, strings_at, string_size)
    exports, i = [], 0
    while i < nsymbols:
        name, value, section, kind, storage, aux = unpack("<8sIhHBB", data, symbols + 18 * i)
        if name[:4] == b"\0" * 4:
            name = cstring(strings, struct.unpack("<I", name[4:])[0])
        else:
            name = name.rstrip(b"\0").decode("ascii")
        if storage == 2 and section > 0:
            exports.append((name, section, value, kind))
        i += 1 + aux
    require(i == nsymbols and len(texts) == 1, "unexpected COFF symbols/sections")
    require(exports == [("crypto_sha256", texts[0][0], 0, 0x20)], "unexpected COFF exports")
    return texts[0][1]


def text_bytes(data):
    if data.startswith(b"\x7fELF"):
        return elf(data)
    if data.startswith(b"\xcf\xfa\xed\xfe"):
        return macho(data)
    return coff(data)


def archive_object(data):
    require(data.startswith(b"!<arch>\n"), "expected static archive")
    offset, members = 8, []
    while offset < len(data):
        header = chunk(data, offset, 60)
        require(header[58:] == b"`\n", "invalid archive header")
        size = int(header[48:58])
        member = chunk(data, offset + 60, size)
        name = header[:16].decode("ascii").strip()
        if name.startswith("#1/"):
            name_bytes = int(name[3:])
            name = chunk(member, 0, name_bytes).rstrip(b"\0").decode("ascii")
            member = member[name_bytes:]
        if name not in ("/", "//", "/SYM64/", "__.SYMDEF", "__.SYMDEF SORTED"):
            require(name.rstrip("/") == "sha256.o", "unexpected archive member")
            members.append(member)
        offset += 60 + size + size % 2
    require(offset == len(data) and len(members) == 1, "expected exactly one archive object")
    return members[0]


def check(root, expected):
    reports = []
    for os in ("linux", "windows", "macos"):
        directory = root / "build" / (os + "-arm64")
        obj = (directory / "sha256.o").read_bytes()
        archive = (directory / "libasm-crypto.a").read_bytes()
        require(archive_object(archive) == obj, os + ": archive differs from object")
        actual = text_bytes(obj)
        require(actual == expected, os + ": instructions/constants differ from recorded program")
        reports.append({"target": os + "-arm64", "object_sha256": hashlib.sha256(obj).hexdigest(),
                        "archive_sha256": hashlib.sha256(archive).hexdigest(),
                        "text_sha256": hashlib.sha256(actual).hexdigest(), "text_bytes": len(actual)})
    return reports


def render_program(expected):
    require(len(expected) == 896, "unexpected ARM64 image length")
    words = struct.unpack("<224I", expected)
    lines = ["import Init.Data.BitVec.Basic", "",
             "/-! Recorded ARM64 image, including code, alignment and SHA-256 constants.",
             "Generated from arm64-sha256.text.hex; no execution correctness is asserted. -/",
             "", "namespace Crypto.ARM64", "",
             "def imageWords : Array (BitVec 32) := #["]
    for i in range(0, len(words), 4):
        lines.append("  " + ", ".join(f"0x{w:08x}#32" for w in words[i:i + 4])
                     + ("," if i + 4 < len(words) else ""))
    lines.extend(["]", "", "def functionBytes : Nat := 604",
                  "def constantsOffset : Nat := 608", "def initialHashOffset : Nat := 864",
                  "", "end Crypto.ARM64", ""])
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    args = parser.parse_args()
    expected_path = args.root / "lean/Models/arm64-sha256.text.hex"
    expected = bytes.fromhex(expected_path.read_text())
    require((args.root / "lean/Models/ARM64Program.lean").read_text() == render_program(expected),
            "Lean program differs from recorded instruction/constant bytes")
    print(json.dumps({"claim": "artifact identity only; equal is not established",
                      "artifacts": check(args.root, expected)}, indent=2))


if __name__ == "__main__":
    main()
