#!/usr/bin/env python3
"""Exercise fail-closed expected-statement/semantic-closure validation.

Temporary manifests exercise the external-pin validator. The dependency audit
checks the real pinned imports.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
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

    def test_generated_heatmap_only_is_ignored(self):
        start = "<!-- CI generates the verification heatmap here. -->"
        end = "<!-- End of the verification heatmap. -->"

        def picture(name, alt, title=None):
            extra = f' title="{title}"' if title else ""
            return (f'<picture><source media="(prefers-color-scheme: dark)" '
                    f'srcset="docs/heatmap/{name}-dark.svg"><img src="docs/heatmap/{name}-light.svg" '
                    f'alt="{alt}"{extra}></picture>')

        def cell(level, text):
            return ('<a href="docs/reference/sha-256.md#function-crypto_sha256">' +
                    picture(f"cell-{level}", "crypto_sha256", f"crypto_sha256: {text}") + "</a>")

        def heatmap(level, text):
            return (start + "\n<table><tr><td>\n\n" +
                    picture("header", f"asm-crypto formal verification: {min(level, 1)} of 1 functions proved") +
                    "\n\n" + picture("label-sha-256", "sha-256") + cell(level, text) + "<br>\n" +
                    picture("label", "") + cell(level, text) + "\n\n" + picture("legend", "Legend") +
                    "\n\n</td></tr></table>\n" + end)

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            path = root / "README.md"
            before, after = "# asm-crypto\n\nStandard: pinned.\n\n", "\n\n## Reference\n"
            path.write_text(before + start + "\n" + end + after)
            initial = pin.source_digest(root, path)
            path.write_text(before + heatmap(0, "Not proved") + after)
            self.assertEqual(initial, pin.source_digest(root, path))
            path.write_text(before + heatmap(1, "Proved on 1 ISA") + after)
            self.assertEqual(initial, pin.source_digest(root, path))
            path.write_text(before + heatmap(1, "Proved on 1 ISA") + after.replace("Reference", "Assumptions"))
            self.assertNotEqual(initial, pin.source_digest(root, path))
            path.write_text(before + heatmap(1, "Proved on 1 ISA").replace("<br>\n", "<br>\nHidden assumption.\n") + after)
            with self.assertRaisesRegex(ValueError, "unrecognized"):
                pin.source_digest(root, path)
            path.write_text(before + heatmap(1, "Proved by fiat") + after)
            with self.assertRaisesRegex(ValueError, "unrecognized"):
                pin.source_digest(root, path)
            path.write_text(before + heatmap(1, "Proved on 1 ISA") + heatmap(1, "Proved on 1 ISA") + after)
            with self.assertRaisesRegex(ValueError, "at most one"):
                pin.source_digest(root, path)


    def test_generated_panels_only_are_ignored(self):
        panels = sys.modules[pin.source_digest.__module__].PANELS

        def picture(name, alt):
            return (f'<picture><source media="(prefers-color-scheme: dark)" '
                    f'srcset="docs/readme/{name}-dark.svg"><img src="docs/readme/{name}-light.svg" '
                    f'alt="{alt}"></picture>')

        def framed(body):
            return "<table><tr><td>\n\n" + body + "\n\n</td></tr></table>\n"

        def card(kind, folder, name):
            return (f'<a href="docs/{folder}/{name}.md">' + picture(f"docs-{kind}-{name}", f"{name}: summary") +
                    "</a>")

        def ci(run, word):
            return framed(f'<a href="https://github.com/bitminetech/asm-crypto/actions/runs/{run}">' +
                          picture("ci", f"Latest CI run {word}: 9 of 9 jobs passed") + "</a>")

        platforms = framed(picture("platforms", "Supported platforms. Linux: x86-64, ARM64, RISC-V; "
                                   "Windows: x86-64, ARM64; macOS 11.0 or later: x86-64, ARM64"))
        docs = framed(picture("docs-header", "asm-crypto docs") + "<br>\n" +
                      picture("docs-docs", "Function docs") + "<br>\n" +
                      card("doc", "reference", "aes") + card("doc", "reference", "sha-256") + "<br>\n" +
                      card("doc", "reference", "x25519") + "\n\n" +
                      picture("docs-models", "Lean models") + "<br>\n" + card("model", "models", "arm64-round") +
                      "\n\n" + picture("docs-footer", "Select a card to open its doc."))

        def readme(blocks, after="\n## End\n"):
            return ("# asm-crypto\n\nStandard: pinned.\n\n" +
                    "\n\n".join(start + "\n" + body + end
                                for body, (start, end) in zip(blocks, panels.values())) + after)

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            path = root / "README.md"
            path.write_text(readme(("", "", "")))
            initial = pin.source_digest(root, path)
            path.write_text(readme((platforms, ci(1, "passed"), docs)))
            self.assertEqual(initial, pin.source_digest(root, path))
            path.write_text(readme((platforms, ci(2, "failed"), docs)))
            self.assertEqual(initial, pin.source_digest(root, path))
            path.write_text(readme((platforms, ci(2, "failed"), docs), after="\n## Assumptions\n"))
            self.assertNotEqual(initial, pin.source_digest(root, path))
            for bad in ((platforms.replace("RISC-V;", "RISC-V, MIPS;"), ci(1, "passed"), docs),
                        (platforms, ci(1, "proved"), docs),
                        (platforms, ci(1, "passed").replace("</a>", "</a>Hidden assumption."), docs),
                        (platforms, ci(1, "passed"), docs.replace("<br>\n", "<br>\nHidden assumption.\n", 1)),
                        (platforms, ci(1, "passed"), docs.replace("docs/reference/aes.md", "https://example.com/a.md"))):
                path.write_text(readme(bad))
                with self.assertRaisesRegex(ValueError, "unrecognized"):
                    pin.source_digest(root, path)
            path.write_text(readme((platforms, ci(1, "passed"), docs)) + panels["CI panel"][0])
            with self.assertRaisesRegex(ValueError, "at most one"):
                pin.source_digest(root, path)

if __name__ == "__main__":
    unittest.main()
