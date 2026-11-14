#!/usr/bin/env python3
"""Compare ARM64 objects/archives with the recorded program, without disassembly.

This is an artifact identity check, not a proof of the program's behavior.
The extraction/parsing code and unwind interpretation are trusted until their
correspondence is proved. Object metadata is checked before linking; final link,
loaded permissions/addresses, unwind registration and runtime binding are not
established by these checks.
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


# Pinned LLVM object encodings of the leaf's unwind description. Both DWARF
# records use SP as CFA, LR/X30 as return address, cover [0,604), and change CFA
# offset from 0 to 416 at instruction offset4 and back to0 at offset600.
ELF_UNWIND = bytes.fromhex(
    "1000000000000000017a5200017c1e011b0c1f00"
    "1800000018000000000000005c02000000440ea0030354020e000000")
MACHO_UNWIND = bytes.fromhex(
    "1000000000000000017a520001781e01100c1f00"
    "2000000018000000e4ffffffffffffff5c0200000000000000440ea0030354020e000000")
# Windows packed unwind: FunctionLength151*4=604, FrameSize26*16=416,
# no saved FP/GPR registers, no parameter homing, leaf CR=0.
COFF_PACKED_UNWIND = bytes.fromhex("000000005d02000d")
# Mach-O object fallback record: function start relocation, length604, DWARF
# mode, no personality/LSDA. The final linker must resolve the DWARF FDE offset.
MACHO_COMPACT_UNWIND = bytes.fromhex(
    "00000000000000005c0200000000000300000000000000000000000000000000")


def alignment(value, minimum, label):
    require(value >= minimum and value & (value - 1) == 0, label + " alignment")


def elf(data):
    require(data[:7] == b"\x7fELF\x02\x01\x01", "expected little-endian ELF64")
    kind, machine = unpack("<HH", data, 16)
    require((kind, machine) == (1, 183), "expected AArch64 relocatable ELF")
    table, = unpack("<Q", data, 40)
    stride, count, names_index = unpack("<HHH", data, 58)
    require(stride == 64 and 0 < names_index < count, "invalid ELF section table")
    sections = [unpack("<IIQQQQIIQQ", data, table + i * stride) for i in range(count)]
    names = chunk(data, sections[names_index][4], sections[names_index][5])
    by_name = {}
    for i, section in enumerate(sections):
        name = cstring(names, section[0])
        require(name not in by_name, "duplicate ELF section")
        by_name[name] = (i, section)
    require(set(by_name) == {"", ".strtab", ".text", ".note.GNU-stack", ".eh_frame",
                             ".rela.eh_frame", ".symtab"}, "unexpected ELF sections")
    for name, (_, section) in by_name.items():
        require(section[3] == 0, "unexpected ELF section address")
        if section[1] in (4, 9):
            require(name == ".rela.eh_frame" and section[1] == 4,
                    "unexpected ELF relocation section")
    require(by_name[""][1] == (0,) * 10, "invalid ELF null section")
    require(by_name[".strtab"][1][1:3] == (3, 0), "invalid ELF string table")
    index, text = by_name[".text"]
    require(text[1:4] == (1, 6, 0), "unexpected ELF text type/permissions/address")
    alignment(text[8], 16, "ELF text")
    _, stack = by_name[".note.GNU-stack"]
    require(stack[1] == 1 and stack[2] == 0 and stack[5] == 0, "ELF executable stack marker")
    unwind_index, unwind = by_name[".eh_frame"]
    require(unwind[1] == 1 and unwind[2] == 2 and unwind[8] == 8 and
            chunk(data, unwind[4], unwind[5]) == ELF_UNWIND, "ELF unwind description")
    sym_index, symtab = by_name[".symtab"]
    require(symtab[1:3] == (2, 0) and symtab[9] == 24 and symtab[5] % 24 == 0 and
            symtab[6] < count, "invalid ELF symbols")
    strings = sections[symtab[6]]
    strings = chunk(data, strings[4], strings[5])
    symbols, exports = [], []
    for offset in range(symtab[4], symtab[4] + symtab[5], 24):
        name, info, other, section, value, size = unpack("<IBBHQQ", data, offset)
        name = cstring(strings, name)
        symbols.append((name, info, other, section, value, size))
        require(info >> 4 in (0, 1), "ELF weak/unsupported symbol binding")
        if info >> 4 == 1:
            require(section != 0, "undefined ELF external")
            require(info >> 4 == 1 and other == 0, "ELF weak/hidden export")
            exports.append((name, section, value, size, info & 15))
    require(exports == [("crypto_sha256", index, 0, 604, 2)], "unexpected ELF exports")
    _, rel = by_name[".rela.eh_frame"]
    require(rel[1:3] == (4, 0x40) and rel[5] == 24 and rel[6] == sym_index and
            rel[7] == unwind_index and rel[9] == 24, "ELF metadata relocation table")
    address, info, addend = unpack("<QQq", data, rel[4])
    symbol = info >> 32
    require(address == 28 and info & 0xffffffff == 261 and addend == 0 and
            symbol < len(symbols), "ELF metadata relocation")
    target = symbols[symbol]
    require(target[1:] == (3, 0, index, 0, 0), "ELF metadata relocation target")
    return chunk(data, text[4], text[5])


def macho(data):
    magic, cpu, subtype, kind, ncommands, command_bytes, _, _ = unpack("<8I", data, 0)
    require((magic, cpu, subtype, kind) == (0xfeedfacf, 0x100000c, 0, 1),
            "expected ARM64 Mach-O object")
    end = 32 + command_bytes
    chunk(data, 32, command_bytes)
    offset, section_index = 32, 0
    sections, symbols, exports, commands = {}, [], [], []
    dysymtab = None
    for _ in range(ncommands):
        cmd, length = unpack("<II", data, offset)
        require(length >= 8 and offset + length <= end, "invalid Mach-O load command")
        commands.append(cmd)
        if cmd == 0x19:  # LC_SEGMENT_64
            nsections, = unpack("<I", data, offset + 64)
            require(length == 72 + 80 * nsections, "invalid Mach-O segment")
            for j in range(nsections):
                section = unpack("<16s16sQQ8I", data, offset + 72 + j * 80)
                section_index += 1
                name = section[0].rstrip(b"\0")
                require(name not in sections, "duplicate Mach-O section")
                sections[name] = (section_index, section)
        elif cmd == 2:  # LC_SYMTAB
            require(length == 24, "invalid Mach-O symtab command")
            symbol_offset, nsymbols, string_offset, string_bytes = unpack("<4I", data, offset + 8)
            strings = chunk(data, string_offset, string_bytes)
            for i in range(nsymbols):
                name, kind_bits, section, desc, value = unpack("<IBBHQ", data, symbol_offset + 16 * i)
                name = cstring(strings, name)
                symbols.append((name, kind_bits, section, desc, value))
                if kind_bits & 1:
                    require(kind_bits == 0x0f and desc == 0, "Mach-O undefined/weak external")
                    exports.append((name, section, value, kind_bits & 0x0e))
        elif cmd == 0x32:  # LC_BUILD_VERSION
            require(length == 24 and unpack("<4I", data, offset + 8) == (1, 0x000b0000, 0, 0),
                    "unexpected Mach-O target version")
        elif cmd == 0xb:  # LC_DYSYMTAB; symbols/relocations are checked separately.
            require(length == 80, "invalid Mach-O dysymtab command")
            dysymtab = unpack("<18I", data, offset + 8)
        else:
            require(False, "unexpected Mach-O load command")
        offset += length
    require(offset == end and sorted(commands) == [2, 0xb, 0x19, 0x32],
            "unexpected Mach-O command count")
    require(dysymtab == (0, len(symbols) - 1, len(symbols) - 1, 1, len(symbols), 0) + (0,) * 12,
            "Mach-O dynamic symbols/metadata relocation tables")
    require(set(sections) == {b"__text", b"__compact_unwind", b"__eh_frame"},
            "unexpected Mach-O sections")
    text_index, text = sections[b"__text"]
    require(text[1].rstrip(b"\0") == b"__TEXT" and text[2] == 0 and
            text[7] == 0 and text[8] == 0x80000400, "Mach-O text address/relocations/flags")
    alignment(1 << text[5] if text[5] < 64 else 0, 16, "Mach-O text")
    require(exports == [("_crypto_sha256", text_index, 0, 0x0e)], "unexpected Mach-O exports")
    unwind_index, unwind = sections[b"__eh_frame"]
    _, compact = sections[b"__compact_unwind"]
    require(compact[1].rstrip(b"\0") == b"__LD" and compact[5] == 3 and
            compact[8] == 0x02000000 and
            chunk(data, compact[4], compact[3]) == MACHO_COMPACT_UNWIND,
            "Mach-O compact unwind description")
    require(unwind[1].rstrip(b"\0") == b"__TEXT" and unwind[5] == 3 and
            unwind[8] == 0x6800000b and
            chunk(data, unwind[4], unwind[3]) == MACHO_UNWIND, "Mach-O unwind description")
    require(compact[7] == 1 and unwind[7] == 2, "Mach-O metadata relocation count")
    require(unpack("<II", data, compact[6]) == (0, (3 << 25) | text_index),
            "Mach-O compact metadata relocation")
    subtract_address, subtract_info = unpack("<II", data, unwind[6])
    add_address, add_info = unpack("<II", data, unwind[6] + 8)
    require(subtract_address == add_address == 28 and
            subtract_info >> 24 == 0x1e and add_info >> 24 == 0x0e,
            "Mach-O metadata relocation")
    subtract_target, add_target = subtract_info & 0xffffff, add_info & 0xffffff
    require(subtract_target < len(symbols) and add_target < len(symbols),
            "Mach-O metadata relocation symbol")
    require(symbols[subtract_target][1:] == (0x0e, unwind_index, 0, unwind[2]) and
            symbols[add_target] == ("_crypto_sha256", 0x0f, text_index, 0, 0),
            "Mach-O metadata relocation target")
    return chunk(data, text[4], text[3])


def coff(data):
    machine, count, _, symbols_at, nsymbols, optional_bytes, _ = unpack("<HHIIIHH", data, 0)
    require(machine == 0xaa64 and optional_bytes == 0, "expected ARM64 COFF object")
    sections = {}
    for i in range(count):
        section = unpack("<8s6I2HI", data, 20 + 40 * i)
        name = section[0].rstrip(b"\0")
        require(name not in sections, "duplicate COFF section")
        sections[name] = (i + 1, section)
    require(set(sections) == {b".text", b".data", b".bss", b".pdata", b".xdata"},
            "unexpected COFF sections")
    text_index, text = sections[b".text"]
    require(text[1] == text[2] == text[7] == 0 and
            text[9] & ~0x00f00000 == 0x60000020, "COFF text address/relocations/flags")
    encoded_alignment = (text[9] >> 20) & 15
    alignment(1 << (encoded_alignment - 1) if encoded_alignment else 0, 16, "COFF text")
    for name, flags in ((b".data", 0xc0300040), (b".bss", 0xc0300080), (b".xdata", 0x40300040)):
        section = sections[name][1]
        require(section[1] == section[2] == section[3] == section[7] == 0 and section[9] == flags,
                "unexpected COFF data/metadata content")
    _, pdata = sections[b".pdata"]
    require(pdata[1] == pdata[2] == 0 and pdata[9] == 0x40300040 and pdata[7] == 1 and
            chunk(data, pdata[4], pdata[3]) == COFF_PACKED_UNWIND, "COFF unwind description")
    strings_at = symbols_at + 18 * nsymbols
    string_size, = unpack("<I", data, strings_at)
    strings = chunk(data, strings_at, string_size)
    symbols, exports, i = {}, [], 0
    while i < nsymbols:
        name, value, section, kind, storage, aux = unpack("<8sIhHBB", data, symbols_at + 18 * i)
        if name[:4] == b"\0" * 4:
            name = cstring(strings, struct.unpack("<I", name[4:])[0])
        else:
            name = name.rstrip(b"\0").decode("ascii")
        symbols[i] = (name, value, section, kind, storage, aux)
        require(storage in (2, 3), "COFF weak/unsupported symbol storage")
        if storage == 2:
            require(section > 0, "COFF undefined external")
            exports.append((name, section, value, kind))
        i += 1 + aux
    require(i == nsymbols, "unexpected COFF symbol count")
    require(exports == [("crypto_sha256", text_index, 0, 0x20)], "unexpected COFF exports")
    address, target, kind = unpack("<IIH", data, pdata[5])
    require(address == 0 and kind == 2 and target in symbols, "COFF metadata relocation")
    require(symbols[target] == (".text", 0, text_index, 0, 3, 1), "COFF metadata relocation target")
    return chunk(data, text[4], text[3])


def text_bytes(data):
    if data.startswith(b"\x7fELF"):
        return elf(data)
    if data.startswith(b"\xcf\xfa\xed\xfe"):
        return macho(data)
    return coff(data)


# The objects of the library archive, one for each core file. Only sha256.o is
# compared with the recorded program; the others must be present once each.
CORE_OBJECTS = ("sha256.o", "keccak.o", "hmac.o", "aes.o", "secp256k1.o", "chacha20.o", "x25519.o", "p256.o", "sha512.o", "ed25519.o")


def archive_object(data):
    """The sha256.o member of the archive, after checking the member list."""
    require(data.startswith(b"!<arch>\n"), "expected static archive")
    offset, members = 8, {}
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
            name = name.rstrip("/")
            require(name in CORE_OBJECTS and name not in members, "unexpected archive member")
            members[name] = member
        offset += 60 + size + size % 2
    require(offset == len(data) and set(members) == set(CORE_OBJECTS), "expected each core object once")
    return members["sha256.o"]


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
                        "text_sha256": hashlib.sha256(actual).hexdigest(), "text_bytes": len(actual), "text_alignment_at_least": 16,
                        "entry_offset": 0, "function_bytes": 604,
                        "object_unwind_checked": True, "metadata_relocations_checked": True,
                        "final_link_and_runtime_binding_checked": False})
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
                      "unwind_scope": "Pinned relocatable-object descriptions and metadata relocation targets only; final linked unwind tables and registration are not checked",
                      "trust": "Python object/archive parsers and interpretation of pinned LLVM unwind encodings",
                      "artifacts": check(args.root, expected)}, indent=2))


if __name__ == "__main__":
    main()
