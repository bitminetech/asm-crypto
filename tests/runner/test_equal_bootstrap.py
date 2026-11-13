#!/usr/bin/env python3
"""Negative tests for the trusted bootstrap; all manifests here are fixtures."""
import base64
import copy
import hashlib
import importlib.util
import json
import py_compile
import shutil
import subprocess
import sys
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("equal_bootstrap", Path(__file__).with_name("check_arm64_equal_bootstrap.py"))
bootstrap = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bootstrap)


class BootstrapTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.paths = []
        for relative in bootstrap.BOOTSTRAP_SOURCES:
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("# fixture validator\n")
            self.paths.append(path)
        self.definition = self.root / "Definitions.lean"
        self.definition.write_text("-- fixture semantic source\n")
        self.paths.append(self.definition)
        self.manifest = {"schema": 1, "theorem": "Crypto.ARM64.sha256.equal", "expected_statement": "fixture",
                         "source_sha256": {str(p.relative_to(self.root)): self.digest(p) for p in self.paths}}
        self.prepare = SimpleNamespace(EXPECTED="fixture", source_paths=lambda root: self.paths,
                                       source_digest=lambda root, path: self.digest(path))

    @staticmethod
    def digest(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def test_external_hash_is_mandatory(self):
        raw = json.dumps(self.manifest).encode()
        encoded = base64.b64encode(raw).decode()
        with self.assertRaisesRegex(ValueError, "SHA-256 differs"):
            bootstrap.selected_manifest(encoded, "0" * 64)
        selected = hashlib.sha256(raw).hexdigest()
        self.assertEqual(bootstrap.selected_manifest(encoded, selected), self.manifest)

    def test_all_three_raw_pins_precede_any_candidate_import(self):
        sentinel = self.root / "executed"
        first = self.root / bootstrap.BOOTSTRAP_SOURCES[0]
        first.write_text("from pathlib import Path\nPath(" + repr(str(sentinel)) + ").write_text('executed')\n")
        self.manifest["source_sha256"][bootstrap.BOOTSTRAP_SOURCES[0]] = self.digest(first)
        last = self.root / bootstrap.BOOTSTRAP_SOURCES[-1]
        last.write_text("# modified after pin\n")
        with self.assertRaisesRegex(ValueError, "bootstrap validator"):
            bootstrap.verify_candidate_sources(self.root, self.manifest)
        self.assertFalse(sentinel.exists())

    def test_reject_modified_first_validator_without_import(self):
        self.paths[0].write_text("raise RuntimeError('must not execute')\n")
        with patch.object(bootstrap, "load_module") as load:
            with self.assertRaisesRegex(ValueError, "bootstrap validator"):
                bootstrap.verify_candidate_sources(self.root, self.manifest)
            load.assert_not_called()

    def test_reject_omitted_validator(self):
        del self.manifest["source_sha256"][bootstrap.BOOTSTRAP_SOURCES[1]]
        with patch.object(bootstrap, "load_module") as load:
            with self.assertRaisesRegex(ValueError, "bootstrap validator"):
                bootstrap.verify_candidate_sources(self.root, self.manifest)
            load.assert_not_called()

    def test_reject_changed_semantics_after_bootstrap_pin(self):
        self.definition.write_text("-- changed semantic source\n")
        with patch.object(bootstrap, "load_module", return_value=self.prepare):
            with self.assertRaisesRegex(ValueError, "semantic source differs"):
                bootstrap.verify_candidate_sources(self.root, self.manifest)

    def test_reject_extra_or_omitted_closure_path(self):
        self.manifest["source_sha256"].pop("Definitions.lean")
        with patch.object(bootstrap, "load_module", return_value=self.prepare):
            with self.assertRaisesRegex(ValueError, "closure path set"):
                bootstrap.verify_candidate_sources(self.root, self.manifest)

    def test_reject_unrelated_expected_statement(self):
        self.manifest["expected_statement"] = "example : True := True.intro"
        with patch.object(bootstrap, "load_module", return_value=self.prepare):
            with self.assertRaisesRegex(ValueError, "complete registered baseline"):
                bootstrap.verify_candidate_sources(self.root, self.manifest)

    def test_reject_source_escape_before_import(self):
        self.manifest["source_sha256"]["../outside"] = "0" * 64
        with patch.object(bootstrap, "load_module") as load:
            with self.assertRaisesRegex(ValueError, "escapes candidate"):
                bootstrap.verify_candidate_sources(self.root, self.manifest)
            load.assert_not_called()


    def test_loader_ignores_unchecked_hash_bytecode(self):
        sentinel = self.root / "bytecode-executed"
        source = self.root / "cached.py"
        source.write_text("from pathlib import Path\nPath(" + repr(str(sentinel)) + ").write_text('bad')\nvalue = 666\n")
        py_compile.compile(str(source), doraise=True, invalidation_mode=py_compile.PycInvalidationMode.UNCHECKED_HASH)
        source.write_text("value = 1\n")
        module = bootstrap.load_module("_bootstrap_cache_fixture", source)
        self.assertEqual(module.value, 1)
        self.assertFalse(sentinel.exists())

    def test_loader_restores_path_before_next_standard_import(self):
        sentinel = self.root / "package-executed"
        runner = self.root / "runner"
        package = runner / "glob"
        package.mkdir(parents=True)
        (package / "__init__.py").write_text(
            "from pathlib import Path\nPath(" + repr(str(sentinel)) + ").write_text('bad')\n")
        first, second = self.root / "first.py", self.root / "second.py"
        first.write_text("import sys\nsys.path.insert(0, " + repr(str(runner)) + ")\n")
        second.write_text("import glob\n")
        previous_path = sys.path[:]
        bootstrap.load_module("_bootstrap_path_fixture", first)
        self.assertEqual(sys.path, previous_path)
        previous_glob = sys.modules.pop("glob", None)
        try:
            module = bootstrap.load_module("_bootstrap_standard_fixture", second)
            self.assertFalse(Path(module.glob.__file__).is_relative_to(runner))
            self.assertFalse(sentinel.exists())
        finally:
            sys.modules.pop("glob", None)
            if previous_glob is not None:
                sys.modules["glob"] = previous_glob

    def test_registered_workflow_and_repository_identity(self):
        registered = {"id": 123, "path": ".github/workflows/ci.yml"}
        run = {"id": 456, "workflow_id": 123, "path": ".github/workflows/ci.yml@main",
               "head_sha": "1" * 40, "conclusion": "success", "event": "push",
               "repository": {"id": 1, "full_name": "fixture/repo"},
               "head_repository": {"id": 1, "full_name": "fixture/repo"}}
        self.assertEqual(bootstrap.validate_ci_run(run, registered, "fixture/repo"), ("1" * 40, 456))
        for field, value in (("path", ".github/workflows/fake-ci.yaml"), ("workflow_id", 999),
                             ("repository", {"id": 2, "full_name": "other/repo"}),
                             ("head_repository", {"id": 2, "full_name": "other/repo"})):
            with self.subTest(field=field):
                altered = copy.deepcopy(run)
                altered[field] = value
                with self.assertRaises(ValueError):
                    bootstrap.validate_ci_run(altered, registered, "fixture/repo")
        with self.assertRaisesRegex(ValueError, "commit differs"):
            bootstrap.validate_ci_run(run, registered, "fixture/repo", "2" * 40)
        run["event"] = "pull_request"
        run["head_repository"] = {"id": 2, "full_name": "fixture/fork"}
        with self.assertRaisesRegex(ValueError, "not linked"):
            bootstrap.validate_ci_run(run, registered, "fixture/repo")
        run["pull_requests"] = [{"head": {"sha": "1" * 40, "repo": {"id": 2}},
                                 "base": {"repo": {"id": 1}}}]
        self.assertEqual(bootstrap.validate_ci_run(run, registered, "fixture/repo"), ("1" * 40, 456))

    def test_validate_real_modules_with_sibling_build_directory(self):
        # Run the real source bootstrap, receipt constructor and table validator.
        # Only the synthetic checkout's Git metadata query is substituted.
        repository = Path(__file__).resolve().parents[2]
        prepare = bootstrap.load_module("_fixture_prepare", repository / bootstrap.BOOTSTRAP_SOURCES[0])
        candidate, build, evidence = self.root / "candidate", self.root / "downloaded-build", self.root / "evidence"
        candidate.mkdir()
        evidence.mkdir()
        for path in prepare.source_paths(repository):
            target = candidate / path.relative_to(repository)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
        sources = {str(path.relative_to(candidate)): prepare.source_digest(candidate, path)
                   for path in prepare.source_paths(candidate)}
        manifest = {"schema": 1, "theorem": "Crypto.ARM64.sha256.equal",
                    "expected_statement": prepare.EXPECTED, "source_sha256": sources}
        selected = hashlib.sha256(json.dumps(manifest).encode()).hexdigest()
        image = bytes.fromhex((candidate / "lean/Models/arm64-sha256.text.hex").read_text())
        artifacts = []
        for target in ("linux-arm64", "windows-arm64", "macos-arm64"):
            directory = build / target
            directory.mkdir(parents=True)
            obj, archive = ("fixture-object:" + target).encode(), ("fixture-archive:" + target).encode()
            (directory / "sha256.o").write_bytes(obj)
            (directory / "libasm-crypto.a").write_bytes(archive)
            artifacts.append({"target": target, "object_sha256": hashlib.sha256(obj).hexdigest(),
                              "archive_sha256": hashlib.sha256(archive).hexdigest(),
                              "text_sha256": hashlib.sha256(image).hexdigest(), "text_bytes": 896,
                              "function_bytes": 604, "entry_offset": 0, "text_alignment_at_least": 16,
                              "object_unwind_checked": True, "metadata_relocations_checked": True,
                              "final_link_and_runtime_binding_checked": False})
        support = {"supporting_checks": "passed", "kernel_replay": "fresh kernel; successful exit",
                   "axiom_audit": ["AXIOMS PASS Crypto.ARM64.sha256.equal: fixture"],
                   "source_sha256": sources, "git_commit": "1" * 40,
                   "arm64_artifact_identity": {"artifacts": artifacts}}
        (evidence / "status.json").write_text(json.dumps(support))
        bootstrap.verify_candidate_sources(candidate, manifest)
        checker = bootstrap.load_module("_fixture_checker", candidate / bootstrap.BOOTSTRAP_SOURCES[1])
        receipt = checker.checked_receipt(candidate, manifest, selected, support, build_dir=build)
        (evidence / "checked-equal.json").write_text(json.dumps(receipt))
        self.assertFalse((candidate / "build").exists())
        with patch.object(subprocess, "check_output", return_value="1" * 40 + "\n"):
            self.assertEqual(bootstrap.validate(candidate, evidence, build, manifest, selected), receipt)
        (build / "windows-arm64/sha256.o").write_bytes(b"changed artifact")
        with self.assertRaisesRegex(ValueError, "artifact bytes are stale"):
            bootstrap.validate(candidate, evidence, build, manifest, selected)


if __name__ == "__main__":
    unittest.main()
