#!/usr/bin/env python3
"""Fail-closed consumption of synthetic CI receipts; fixtures prove no claim."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("tick_tables", Path(__file__).with_name("tick_tables.py"))
tick = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tick)


def digest(data):
    return hashlib.sha256(data).hexdigest()


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.build = self.root / "build"
        self.results = self.root / "results"
        self.results.mkdir()
        self.source = self.root / "lean/Proofs/ARM64/NativeEqual.lean"
        self.source.parent.mkdir(parents=True)
        self.source.write_text("-- synthetic source fixture\n")
        self.image = self.root / "lean/Models/arm64-sha256.text.hex"
        self.image.parent.mkdir(parents=True)
        self.image.write_text((b"\x00" * 896).hex())
        artifacts = []
        for target in tick.ARM64_TARGETS:
            directory = self.build / target
            directory.mkdir(parents=True)
            obj, archive = ("object:" + target).encode(), ("archive:" + target).encode()
            (directory / "sha256.o").write_bytes(obj)
            (directory / "libasm-crypto.a").write_bytes(archive)
            artifacts.append({"target": target, "object_sha256": digest(obj), "archive_sha256": digest(archive),
                              "text_sha256": digest(b"\x00" * 896), "text_bytes": 896,
                              "text_alignment_at_least": 16, "entry_offset": 0, "function_bytes": 604,
                              "object_unwind_checked": True, "metadata_relocations_checked": True,
                              "final_link_and_runtime_binding_checked": False})
            os_name, isa = target.split("-")
            (self.results / f"results-{os_name}-{isa}.txt").write_text("FUNCTION crypto_sha256 PASS\n")
        self.commit = "1" * 40
        self.receipt = {"schema": 1, "function": "crypto_sha256", "proof_id": "equal", "isa": "arm64",
                        "theorem": "Crypto.ARM64.sha256.equal", "checked": True,
                        "targets": list(tick.ARM64_TARGETS), "expected_manifest_sha256": "2" * 64,
                        "expected_statement_sha256": digest(tick.EXPECTED.encode()),
                        "source_sha256": {str(self.source.relative_to(self.root)): digest(self.source.read_bytes())},
                        "artifacts": artifacts, "supporting_checks": "passed",
                        "kernel_replay": "fresh kernel; successful exit", "statement_comparison": "passed",
                        "git_commit": self.commit}
        self.path = self.root / "checked-equal.json"
        self.git_patch = patch.object(tick.subprocess, "check_output", return_value=self.commit + "\n")
        self.git_patch.start()
        self.addCleanup(self.git_patch.stop)
        self.graphs = {isa: {} for isa, _ in tick.ISAS}

    def write(self):
        self.path.write_text(json.dumps(self.receipt))
        return self.path

    def valid(self):
        return tick.validate_equal_receipt(self.write(), self.build, self.root)

    def test_current_complete_receipt(self):
        self.assertTrue(self.valid())
        table = tick.table("crypto_sha256", "L2", self.results, self.graphs, {}, True)
        self.assertIn("| ARM64 | ✅ | ✅ | ✅ | ✅ |", table)
        self.assertIn("| x86-64 |  |  |  |  |", table)
        self.assertIn("| RISC-V |  |  |  |  |", table)
        self.assertNotIn("| ARM64 | ✅ | ✅ | ✅ | ✅ |",
                         tick.table("another_function", "L2", self.results, self.graphs, {}, True))

    def test_missing_receipt_keeps_runtime_results(self):
        self.assertFalse(tick.checked_equal(None, self.build, self.root))
        table = tick.table("crypto_sha256", "L2", self.results, self.graphs, {})
        self.assertIn("| ARM64 | ✅ | ✅ | ✅ |  |", table)

    def test_missing_native_results_blocks_proof_tick(self):
        (self.results / "results-windows-arm64.txt").unlink()
        self.assertNotIn("| ARM64 | ✅ | ✅ | ✅ | ✅ |",
                         tick.table("crypto_sha256", "L2", self.results, self.graphs, {}, True))
        self.assertIn("| ARM64 | ✅ |  | ✅ |  |",
                      tick.table("crypto_sha256", "L2", self.results, self.graphs, {}, True))

    def test_reject_incomplete_or_wrong_claims(self):
        changes = [("checked", False), ("schema", True), ("function", "other"), ("isa", "x86_64"),
                   ("targets", tick.ARM64_TARGETS[:2]), ("statement_comparison", "failed"),
                   ("kernel_replay", "not performed"), ("expected_statement_sha256", "0" * 64),
                   ("expected_manifest_sha256", ""), ("git_commit", "0" * 40), ("source_sha256", {})]
        original = copy.deepcopy(self.receipt)
        for key, value in changes:
            with self.subTest(key=key):
                self.receipt = copy.deepcopy(original)
                self.receipt[key] = value
                with self.assertRaises(ValueError):
                    self.valid()

    def test_reject_stale_semantics(self):
        self.write()
        self.source.write_text("-- changed semantic source\n")
        with self.assertRaisesRegex(ValueError, "semantic dependency"):
            tick.validate_equal_receipt(self.path, self.build, self.root)

    def test_reject_stale_build(self):
        self.write()
        (self.build / "macos-arm64/sha256.o").write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "artifact differs"):
            tick.validate_equal_receipt(self.path, self.build, self.root)

    def test_reject_incomplete_artifact_checks(self):
        self.receipt["artifacts"][1]["object_unwind_checked"] = False
        with self.assertRaisesRegex(ValueError, "image/unwind"):
            self.valid()

    def test_reject_source_escape(self):
        self.receipt["source_sha256"]["../outside"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "semantic dependency"):
            self.valid()

    def test_malformed_receipt_leaves_proof_empty(self):
        self.path.write_text("{broken")
        with patch.object(tick, "print"):
            self.assertFalse(tick.checked_equal(self.path, self.build, self.root))


if __name__ == "__main__":
    unittest.main()
