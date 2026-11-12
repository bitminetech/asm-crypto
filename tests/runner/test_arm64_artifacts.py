"""Negative checks for the verification artifact boundary, using real objects."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("artifacts", HERE / "check_arm64_artifacts.py")
artifacts = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(artifacts)
ROOT = HERE.parents[1]
EXPECTED = bytes.fromhex((ROOT / "lean/Models/arm64-sha256.text.hex").read_text())


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
