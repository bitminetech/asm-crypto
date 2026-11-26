#!/usr/bin/env python3
"""Exercise the boundary between the scalar proof image and the shipped archives."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_x86_sha256_artifacts import OBJECTS, ROOT, archive_member, check_target


class ScalarImage(unittest.TestCase):
    def test_redirected_archive_symbols(self):
        model = (ROOT / "lean/Models/X86SHA256Image.lean").read_text()
        for target in OBJECTS:
            folder = ROOT / "build" / (target + "-x86_64")
            archive = (folder / "libasm-crypto.a").read_bytes()
            member = (folder / "sha256.o").read_bytes()
            report = check_target(target, archive, member, model)
            start = report["archive_member_offset"]
            _, _, following = archive_member(archive, start)
            _, primary, second = archive_member(archive, 8)
            order = "little" if target == "macos" else "big"
            source = start.to_bytes(4, order)
            destination = following.to_bytes(4, order)
            self.assertIn(source, primary)
            redirected = primary.replace(source, destination, 1)
            with self.subTest(target=target, directory="primary"), self.assertRaisesRegex(ValueError, "archive symbol"):
                check_target(target, archive.replace(primary, redirected, 1), member, model)
            if target == "windows":
                _, secondary, _ = archive_member(archive, second)
                source = start.to_bytes(4, "little")
                destination = following.to_bytes(4, "little")
                redirected = secondary.replace(source, destination, 1)
                with self.subTest(target=target, directory="secondary"), self.assertRaisesRegex(ValueError, "disagree"):
                    check_target(target, archive.replace(secondary, redirected, 1), member, model)

    def test_changed_bytes(self):
        model = (ROOT / "lean/Models/X86SHA256Image.lean").read_text()
        for target, (_, offset) in OBJECTS.items():
            folder = ROOT / "build" / (target + "-x86_64")
            member = (folder / "sha256.o").read_bytes()
            archive = (folder / "libasm-crypto.a").read_bytes()
            self.assertEqual(archive.count(member), 1)
            for area in [0, 0x384, 0x390, 0x490]:
                with self.subTest(target=target, offset=area):
                    changed = bytearray(member)
                    changed[offset + area] ^= 1
                    with self.assertRaisesRegex(ValueError, "object/archive mismatch"):
                        check_target(target, archive, changed, model)
                    with self.assertRaisesRegex(ValueError, "unexpected object identity"):
                        check_target(target, archive.replace(member, changed), changed, model)
            with self.subTest(target=target, mismatch="model"):
                with self.assertRaisesRegex(ValueError, "Lean image mismatch"):
                    check_target(target, archive, member, model.replace("0x53", "0x52", 1))


if __name__ == "__main__":
    unittest.main()
