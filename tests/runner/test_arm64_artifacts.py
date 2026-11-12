"""Negative checks for the verification artifact boundary, using real objects."""
import importlib.util
import struct
from pathlib import Path
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("artifacts", HERE / "check_arm64_artifacts.py")
artifacts = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(artifacts)
ROOT = HERE.parents[1]
EXPECTED = bytes.fromhex((ROOT / "lean/Models/arm64-sha256.text.hex").read_text())


def section_locations(data, os):
    """Find mutation positions using the documented object-table layouts."""
    result = {}
    if os == "linux":
        table = struct.unpack_from("<Q", data, 40)[0]
        count, names_index = struct.unpack_from("<HH", data, 60)
        sections = [struct.unpack_from("<IIQQQQIIQQ", data, table + 64 * i)
                    for i in range(count)]
        names = sections[names_index]
        strings = data[names[4]:names[4] + names[5]]
        for i, section in enumerate(sections):
            name = strings[section[0]:].split(b"\0")[0].decode("ascii")
            result[name] = (table + 64 * i, section[4], section[5])
    elif os == "windows":
        count = struct.unpack_from("<H", data, 2)[0]
        for i in range(count):
            header = 20 + 40 * i
            section = struct.unpack_from("<8s6I2HI", data, header)
            result[section[0].rstrip(b"\0").decode("ascii")] = (header, section[4], section[3])
    else:
        count = struct.unpack_from("<I", data, 16)[0]
        offset = 32
        for _ in range(count):
            command, size = struct.unpack_from("<II", data, offset)
            if command == 0x19:
                nsections = struct.unpack_from("<I", data, offset + 64)[0]
                for i in range(nsections):
                    header = offset + 72 + 80 * i
                    section = struct.unpack_from("<16s16sQQ8I", data, header)
                    result[section[0].rstrip(b"\0").decode("ascii")] = (header, section[4], section[3])
            offset += size
    return result


class ArtifactBoundary(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for os in ("linux", "windows", "macos"):
            source = ROOT / "build" / (os + "-arm64")
            dest = self.root / "build" / source.name
            dest.mkdir(parents=True)
            for name in ("sha256.o", "libasm-crypto.a"):
                (dest / name).write_bytes((source / name).read_bytes())

    def change_object_and_archive(self, os, mutate):
        directory = self.root / "build" / (os + "-arm64")
        path = directory / "sha256.o"
        before = path.read_bytes()
        after = mutate(before)
        archive = directory / "libasm-crypto.a"
        contents = archive.read_bytes()
        self.assertEqual(contents.count(before), 1)
        archive.write_bytes(contents.replace(before, after))
        path.write_bytes(after)

    def test_original_objects_and_archives(self):
        self.assertEqual(len(artifacts.check(self.root, EXPECTED)), 3)

    def test_changed_instruction_and_constant_rejected_on_each_os(self):
        for os in ("linux", "windows", "macos"):
            for byte_offset in (0, 608, 864):
                with self.subTest(os=os, byte_offset=byte_offset):
                    def mutate(data):
                        offset = data.index(EXPECTED) + byte_offset
                        return data[:offset] + bytes([data[offset] ^ 1]) + data[offset + 1:]
                    self.change_object_and_archive(os, mutate)
                    with self.assertRaisesRegex(ValueError, "instructions/constants"):
                        artifacts.check(self.root, EXPECTED)
                    # Restore both artifacts for the next independent mutation.
                    for name in ("sha256.o", "libasm-crypto.a"):
                        source = ROOT / "build" / (os + "-arm64") / name
                        (self.root / "build" / source.parent.name / name).write_bytes(source.read_bytes())

    def test_archive_object_mismatch_rejected(self):
        obj = self.root / "build/linux-arm64/sha256.o"
        obj.write_bytes(obj.read_bytes() + b"different")
        with self.assertRaisesRegex(ValueError, "archive differs"):
            artifacts.check(self.root, EXPECTED)

    def test_export_rename_rejected(self):
        self.change_object_and_archive("linux", lambda data: data.replace(b"crypto_sha256\0", b"other_symbol!\0"))
        with self.assertRaisesRegex(ValueError, "exports"):
            artifacts.check(self.root, EXPECTED)

    def assert_bad_metadata(self, os, mutate, pattern):
        self.change_object_and_archive(os, mutate)
        try:
            with self.assertRaisesRegex(ValueError, pattern):
                artifacts.check(self.root, EXPECTED)
        finally:
            source = ROOT / "build" / (os + "-arm64")
            for name in ("sha256.o", "libasm-crypto.a"):
                (self.root / "build" / source.name / name).write_bytes((source / name).read_bytes())

    def test_insufficient_text_alignment_rejected_on_each_os(self):
        for os in ("linux", "windows", "macos"):
            with self.subTest(os=os):
                def mutate(data):
                    edited = bytearray(data)
                    name = "__text" if os == "macos" else ".text"
                    header, _, _ = section_locations(data, os)[name]
                    if os == "linux":
                        struct.pack_into("<Q", edited, header + 48, 4)
                    elif os == "windows":
                        flags = struct.unpack_from("<I", data, header + 36)[0]
                        struct.pack_into("<I", edited, header + 36, (flags & ~0xf00000) | 0x300000)
                    else:
                        struct.pack_into("<I", edited, header + 52, 2)
                    return bytes(edited)
                self.assert_bad_metadata(os, mutate, "alignment")

    def test_wrong_unwind_frame_rejected_on_each_os(self):
        for os in ("linux", "windows", "macos"):
            with self.subTest(os=os):
                def mutate(data):
                    edited = bytearray(data)
                    name = {"linux": ".eh_frame", "windows": ".pdata", "macos": "__eh_frame"}[os]
                    _, start, size = section_locations(data, os)[name]
                    if os == "windows":
                        edited[start + 7] ^= 1  # Change packed frame allocation.
                    else:
                        instruction = data[start:start + size].index(bytes.fromhex("0ea003"))
                        edited[start + instruction + 1] ^= 1  # CFA offset416 becomes417.
                    return bytes(edited)
                self.assert_bad_metadata(os, mutate, "unwind description")

    def test_wrong_metadata_relocation_kind_rejected_on_each_os(self):
        for os in ("linux", "windows", "macos"):
            with self.subTest(os=os):
                def mutate(data):
                    edited = bytearray(data)
                    sections = section_locations(data, os)
                    if os == "linux":
                        _, relocation, _ = sections[".rela.eh_frame"]
                        struct.pack_into("<I", edited, relocation + 8, 262)
                    elif os == "windows":
                        header, _, _ = sections[".pdata"]
                        relocation = struct.unpack_from("<I", data, header + 24)[0]
                        struct.pack_into("<H", edited, relocation + 8, 3)
                    else:
                        header, _, _ = sections["__compact_unwind"]
                        relocation = struct.unpack_from("<I", data, header + 56)[0]
                        info = struct.unpack_from("<I", data, relocation + 4)[0]
                        struct.pack_into("<I", edited, relocation + 4, info | 0x10000000)
                    return bytes(edited)
                self.assert_bad_metadata(os, mutate, "metadata relocation")

    def test_wrong_metadata_relocation_target_rejected_on_each_os(self):
        for os in ("linux", "windows", "macos"):
            with self.subTest(os=os):
                def mutate(data):
                    edited = bytearray(data)
                    sections = section_locations(data, os)
                    if os == "linux":
                        _, relocation, _ = sections[".rela.eh_frame"]
                        struct.pack_into("<I", edited, relocation + 12, 0)  # Null symbol, not.text.
                    elif os == "windows":
                        header, _, _ = sections[".pdata"]
                        relocation = struct.unpack_from("<I", data, header + 24)[0]
                        struct.pack_into("<I", edited, relocation + 4, 2)  # .data section symbol.
                    else:
                        header, _, _ = sections["__compact_unwind"]
                        relocation = struct.unpack_from("<I", data, header + 56)[0]
                        struct.pack_into("<I", edited, relocation + 4, 0x06000002)  # Section2, not.text.
                    return bytes(edited)
                self.assert_bad_metadata(os, mutate, "metadata relocation")

    def test_extra_metadata_relocation_rejected_on_each_os(self):
        for os in ("linux", "windows", "macos"):
            with self.subTest(os=os):
                def mutate(data):
                    edited = bytearray(data)
                    sections = section_locations(data, os)
                    if os == "linux":
                        header, _, _ = sections[".rela.eh_frame"]
                        struct.pack_into("<Q", edited, header + 32, 48)
                    elif os == "windows":
                        header, _, _ = sections[".pdata"]
                        struct.pack_into("<H", edited, header + 32, 2)
                    else:
                        header, _, _ = sections["__compact_unwind"]
                        struct.pack_into("<I", edited, header + 60, 2)
                    return bytes(edited)
                self.assert_bad_metadata(os, mutate, "metadata relocation|unwind description")

    def test_weak_elf_entry_rejected(self):
        def mutate(data):
            edited = bytearray(data)
            _, start, size = section_locations(data, "linux")[".symtab"]
            for offset in range(start, start + size, 24):
                if data[offset + 4] >> 4 == 1:
                    edited[offset + 4] = (2 << 4) | (data[offset + 4] & 15)
                    return bytes(edited)
            self.fail("global function symbol missing from fixture")
        self.assert_bad_metadata("linux", mutate, "symbol binding")

    def test_wrong_macos_compact_unwind_range_rejected(self):
        def mutate(data):
            edited = bytearray(data)
            _, start, _ = section_locations(data, "macos")["__compact_unwind"]
            struct.pack_into("<I", edited, start + 8, 600)
            return bytes(edited)
        self.assert_bad_metadata("macos", mutate, "compact unwind description")

    def test_truncated_objects_rejected(self):
        for os in ("linux", "windows", "macos"):
            data = (ROOT / "build" / (os + "-arm64") / "sha256.o").read_bytes()
            with self.subTest(os=os), self.assertRaises((ValueError, IndexError)):
                artifacts.text_bytes(data[:32])

    def test_lean_image_matches_recorded_bytes(self):
        self.assertEqual((ROOT / "lean/Models/ARM64Program.lean").read_text(),
                         artifacts.render_program(EXPECTED))


if __name__ == "__main__":
    unittest.main()
