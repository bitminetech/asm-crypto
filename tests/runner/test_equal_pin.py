#!/usr/bin/env python3
"""Exercise fail-closed expected-statement/semantic-closure validation.

Temporary manifests are test fixtures, never independent approvals or checked
claims. Dependency execution is covered by the existing real dependency audit.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("equal_pin", Path(__file__).with_name("check_arm64_equal_pin.py"))
pin = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pin)


class PinTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name).resolve()
        self.root = self.directory / "candidate"
        self.root.mkdir()
        self.source = self.root / "Definitions.lean"
        self.source.write_text("def requirement : Prop := True\n")
        self.manifest = {
            "schema": 1,
            "theorem": "Crypto.ARM64.sha256.equal",
            "review": {"reviewer": "test-only", "immutable_source": "test-only", "approved_utc": "test-only"},
            "source_sha256": {"Definitions.lean": hashlib.sha256(self.source.read_bytes()).hexdigest()},
            "expected_statement": pin.EXPECTED}
        self.path = self.directory / "trusted.json"
        self.paths_patch = patch.object(pin, "source_paths", return_value=[self.source])
        self.paths_patch.start()
        self.addCleanup(self.paths_patch.stop)
        self.deps_patch = patch.object(pin, "check", return_value=[])
        self.deps_patch.start()
        self.addCleanup(self.deps_patch.stop)

    def write(self):
        raw = json.dumps(self.manifest).encode()
        self.path.write_bytes(raw)
        return hashlib.sha256(raw).hexdigest()

    def test_selected_statement(self):
        _, statement = pin.validate(self.root, self.path, self.write())
        self.assertEqual(statement, self.manifest["expected_statement"])

    def test_reject_candidate_trust_root(self):
        self.path = self.root / "untrusted.json"
        with self.assertRaisesRegex(ValueError, "outside"):
            pin.validate(self.root, self.path, self.write())

    def test_reject_changed_pin(self):
        self.write()
        with self.assertRaisesRegex(ValueError, "selected SHA-256"):
            pin.validate(self.root, self.path, "0" * 64)

    def test_reject_unreviewed_candidate(self):
        self.manifest["review"] = None
        with self.assertRaisesRegex(ValueError, "independent review"):
            pin.validate(self.root, self.path, self.write())

    def test_reject_wrong_claim(self):
        self.manifest["theorem"] = "other.claim"
        with self.assertRaisesRegex(ValueError, "registered ARM64"):
            pin.validate(self.root, self.path, self.write())

    def test_reject_changed_semantics(self):
        selected = self.write()
        self.source.write_text("def requirement : Prop := False\n")
        with self.assertRaisesRegex(ValueError, "semantic dependency differs"):
            pin.validate(self.root, self.path, selected)

    def test_reject_omitted_dependency(self):
        self.manifest["source_sha256"] = {}
        with self.assertRaisesRegex(ValueError, "closure path set"):
            pin.validate(self.root, self.path, self.write())

    def test_reject_missing_expected_statement(self):
        self.manifest["expected_statement"] = ""
        with self.assertRaisesRegex(ValueError, "statement is missing"):
            pin.validate(self.root, self.path, self.write())

    def test_reject_unrelated_true_statement(self):
        self.manifest["expected_statement"] = "example : True := True.intro\n"
        with self.assertRaisesRegex(ValueError, "full pinned baseline type"):
            pin.validate(self.root, self.path, self.write())


if __name__ == "__main__":
    unittest.main()
