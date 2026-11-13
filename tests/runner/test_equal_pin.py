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
        for target in ("linux-arm64", "windows-arm64", "macos-arm64"):
            directory = self.root / "build" / target
            directory.mkdir(parents=True)
            (directory / "sha256.o").write_bytes(b"object fixture")
            (directory / "libasm-crypto.a").write_bytes(b"archive fixture")
        self.manifest = {
            "schema": 1,
            "theorem": "Crypto.ARM64.sha256.equal",
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

    def test_reject_missing_external_selection(self):
        self.write()
        with self.assertRaisesRegex(ValueError, "externally selected SHA-256"):
            pin.validate(self.root, self.path, "")

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

    def support(self):
        return {"supporting_checks": "passed", "kernel_replay": "fresh kernel; successful exit",
                "axiom_audit": ["AXIOMS PASS Crypto.ARM64.sha256.equal: [propext]"],
                "source_sha256": self.manifest["source_sha256"], "git_commit": "0" * 40,
                "arm64_artifact_identity": {"artifacts": [
                    {"target": target, "object_unwind_checked": True, "metadata_relocations_checked": True,
                     "object_sha256": hashlib.sha256(b"object fixture").hexdigest(),
                     "archive_sha256": hashlib.sha256(b"archive fixture").hexdigest(), "text_sha256": "2" * 64}
                    for target in ("linux-arm64", "windows-arm64", "macos-arm64")]}}

    def test_complete_receipt(self):
        receipt = pin.checked_receipt(self.root, self.manifest, "0" * 64, self.support())
        self.assertTrue(receipt["checked"])
        self.assertNotIn("review", receipt)

    def test_reject_receipt_without_fresh_kernel(self):
        support = self.support()
        support["kernel_replay"] = "missing"
        with self.assertRaisesRegex(ValueError, "fresh kernel"):
            pin.checked_receipt(self.root, self.manifest, "0" * 64, support)

    def test_reject_receipt_without_equal_audit(self):
        support = self.support()
        support["axiom_audit"] = []
        with self.assertRaisesRegex(ValueError, "axiom audit"):
            pin.checked_receipt(self.root, self.manifest, "0" * 64, support)

    def test_reject_stale_support(self):
        self.source.write_text("changed\n")
        with self.assertRaisesRegex(ValueError, "stale"):
            pin.checked_receipt(self.root, self.manifest, "0" * 64, self.support())

    def test_reject_missing_artifact(self):
        support = self.support()
        support["arm64_artifact_identity"]["artifacts"].pop()
        with self.assertRaisesRegex(ValueError, "three exact ARM64"):
            pin.checked_receipt(self.root, self.manifest, "0" * 64, support)

    def test_reject_missing_nonlean_snapshot(self):
        path = self.root / "runner.c"
        path.write_text("int main(void) { return 0; }\n")
        self.manifest["source_sha256"]["runner.c"] = hashlib.sha256(path.read_bytes()).hexdigest()
        support = self.support()
        support["source_sha256"] = {k: v for k, v in support["source_sha256"].items() if k != "runner.c"}
        with self.assertRaisesRegex(ValueError, "snapshot is missing"):
            pin.checked_receipt(self.root, self.manifest, "0" * 64, support)

    def test_reject_replaced_artifact(self):
        (self.root / "build/linux-arm64/sha256.o").write_bytes(b"replaced")
        with self.assertRaisesRegex(ValueError, "artifact bytes are stale"):
            pin.checked_receipt(self.root, self.manifest, "0" * 64, self.support())


class ResultNormalizationTests(unittest.TestCase):
    def test_generated_results_only_are_ignored(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            path = root / "docs/reference/sha-256.md"
            path.parent.mkdir(parents=True)
            before = "# SHA-256\nCaller must supply 32 bytes.\n\n## Results\n\n"
            path.write_text(before + "<!-- CI generates the tick table here. -->\n")
            initial = pin.source_digest(root, path)
            table = ("<!-- CI generates the tick table for each function here. -->\n\n"
                     "### `crypto_sha256`\n\n| ISA | Linux | Windows | macOS | `equal` |\n"
                     "|---|---|---|---|---|\n| x86-64 | ✅ | ✅ | ✅ |  |\n"
                     "| ARM64 | ✅ | ✅ | ✅ | ✅ |\n| RISC-V | ✅ |  |  |  |\n")
            path.write_text(before + table)
            self.assertEqual(initial, pin.source_digest(root, path))
            path.write_text(before.replace("32", "16") + table)
            self.assertNotEqual(initial, pin.source_digest(root, path))
            path.write_text(before + table + "Hidden additional assumption.\n")
            with self.assertRaisesRegex(ValueError, "unrecognized"):
                pin.source_digest(root, path)


if __name__ == "__main__":
    unittest.main()
