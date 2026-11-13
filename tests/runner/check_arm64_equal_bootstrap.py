#!/usr/bin/env python3
"""Trusted default-branch bootstrap for a candidate CI run's technical evidence.

Run this copy from the protected/default branch, never from the candidate being
validated. External manifest selection is a repository policy boundary. This
program stores no personal statements, identities or approval attestations.
"""
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from types import ModuleType

BOOTSTRAP_SOURCES = ("tests/runner/prepare_arm64_equal_review.py",
                     "tests/runner/check_arm64_equal_pin.py",
                     "tests/runner/check_lean_dependencies.py")


def load_module(name, path):
    # Compile the bytes just pinned, never a candidate-supplied .pyc cache.
    module = ModuleType(name)
    module.__file__ = str(path)
    previous_module = sys.modules.get(name)
    previous_path = sys.path[:]
    sys.modules[name] = module
    try:
        exec(compile(path.read_bytes(), str(path), "exec"), module.__dict__)
    except BaseException:
        if previous_module is None:
            sys.modules.pop(name, None)
        else:
            sys.modules[name] = previous_module
        raise
    finally:
        # Candidate scripts add their runner directory for ordinary CLI use.
        # It must not shadow standard modules in subsequent bootstrap imports.
        sys.path[:] = previous_path
    return module



def validate_ci_run(run, registered, repository, expected_sha=None):
    """Accept only the registered CI workflow from the authoritative repo API."""
    if (registered.get("path") != ".github/workflows/ci.yml" or
            type(registered.get("id")) is not int or run.get("workflow_id") != registered["id"] or
            not isinstance(run.get("path"), str) or run["path"].split("@", 1)[0] != ".github/workflows/ci.yml"):
        raise ValueError("candidate run is not the registered CI workflow")
    sha, run_id = run.get("head_sha"), run.get("id")
    repo, head = run.get("repository", {}), run.get("head_repository", {})
    if (run.get("conclusion") != "success" or not isinstance(sha, str) or
            not re.fullmatch(r"[0-9a-f]{40}", sha) or type(run_id) is not int or run_id <= 0 or
            repo.get("full_name") != repository or type(repo.get("id")) is not int or
            not isinstance(head.get("full_name"), str) or type(head.get("id")) is not int):
        raise ValueError("invalid candidate CI run or repository identity")
    if expected_sha is not None and sha != expected_sha:
        raise ValueError("candidate CI commit differs from selected event")
    if run.get("event") == "pull_request":
        linked = any(pr.get("head", {}).get("sha") == sha and
                     pr.get("head", {}).get("repo", {}).get("id") == head["id"] and
                     pr.get("base", {}).get("repo", {}).get("id") == repo["id"]
                     for pr in run.get("pull_requests", []))
        if not linked:
            raise ValueError("candidate PR head repository is not linked to this CI run")
    elif run.get("event") != "push" or head.get("full_name") != repository or head["id"] != repo["id"]:
        raise ValueError("candidate push head repository differs")
    return sha, run_id


def selected_manifest(encoded, selected_hash):
    if not re.fullmatch(r"[0-9a-f]{64}", selected_hash):
        raise ValueError("externally selected manifest SHA-256 is required")
    raw = base64.b64decode(encoded, validate=True)
    if hashlib.sha256(raw).hexdigest() != selected_hash:
        raise ValueError("external manifest SHA-256 differs")
    manifest = json.loads(raw)
    if (not isinstance(manifest, dict) or manifest.get("schema") != 1 or
            manifest.get("theorem") != "Crypto.ARM64.sha256.equal"):
        raise ValueError("external manifest must identify ARM64 SHA-256 equal")
    return manifest


def safe_sources(root, manifest):
    sources = manifest.get("source_sha256")
    if not isinstance(sources, dict) or not sources:
        raise ValueError("external semantic source closure is missing")
    for relative, digest in sources.items():
        if (not isinstance(relative, str) or not isinstance(digest, str) or
                not re.fullmatch(r"[0-9a-f]{64}", digest)):
            raise ValueError("invalid external source digest")
        if not (root / relative).resolve().is_relative_to(root):
            raise ValueError("external semantic source escapes candidate checkout")
    return sources


def verify_candidate_sources(root, manifest):
    """Hash before import: candidate Python has no authority until pin matched."""
    root = root.resolve()
    sources = safe_sources(root, manifest)
    for relative in BOOTSTRAP_SOURCES:
        if relative not in sources or hashlib.sha256((root / relative).read_bytes()).hexdigest() != sources[relative]:
            raise ValueError("bootstrap validator source differs: " + relative)
    prepare = load_module("prepare_arm64_equal_review", root / BOOTSTRAP_SOURCES[0])
    expected_paths = {str(p.relative_to(root)) for p in prepare.source_paths(root)}
    if set(sources) != expected_paths:
        raise ValueError("external semantic closure path set differs")
    for relative, digest in sources.items():
        if prepare.source_digest(root, root / relative) != digest:
            raise ValueError("external semantic source differs: " + relative)
    if manifest.get("expected_statement") != prepare.EXPECTED:
        raise ValueError("external expected statement differs from complete registered baseline")
    return prepare


def validate(root, evidence, build, manifest, selected_hash):
    root, evidence, build = root.resolve(), evidence.resolve(), build.resolve()
    verify_candidate_sources(root, manifest)
    # All candidate sources are now matched to the external immutable pin.
    load_module("check_lean_dependencies", root / BOOTSTRAP_SOURCES[2])
    checker = load_module("check_arm64_equal_pin", root / BOOTSTRAP_SOURCES[1])
    tables = load_module("tick_tables", root / "tests/runner/tick_tables.py")
    support = json.loads((evidence / "status.json").read_text())
    receipt = json.loads((evidence / "checked-equal.json").read_text())
    expected = checker.checked_receipt(root, manifest, selected_hash, support, build_dir=build)
    if receipt != expected:
        raise ValueError("CI technical receipt differs from completed pinned proof evidence")
    tables.validate_equal_receipt(evidence / "checked-equal.json", build, root)
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", required=True, type=Path)
    parser.add_argument("--evidence", required=True, type=Path)
    parser.add_argument("--build", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    args.output.unlink(missing_ok=True)
    selected_hash = os.environ.get("EXPECTED_MANIFEST_SHA256", "")
    manifest = selected_manifest(os.environ.get("EXPECTED_MANIFEST_B64", ""), selected_hash)
    receipt = validate(args.candidate, args.evidence, args.build, manifest, selected_hash)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print("Pinned ARM64 SHA-256 sources, proof evidence and exact artifacts matched.")


if __name__ == "__main__":
    main()
