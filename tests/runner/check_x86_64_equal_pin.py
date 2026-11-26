#!/usr/bin/env python3
"""Check the externally selected scalar x86-64 statement and exact build evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_lean_dependencies import check as check_dependencies
from check_x86_sha256_artifacts import check as check_artifacts
from prepare_x86_64_equal_review import EXPECTED, THEOREM, source_digest, source_paths

TARGETS = ["linux-x86_64", "macos-x86_64", "windows-x86_64"]
RECEIPT = "checked-equal-x86_64.json"


def validate_sources(root, manifest):
    expected = {"schema": 1, "function": "crypto_sha256", "proof_id": "equal", "isa": "x86-64",
                "profile": "scalar baseline", "targets": TARGETS, "theorem": THEOREM,
                "expected_statement": EXPECTED}
    if not isinstance(manifest, dict) or any(manifest.get(k) != v for k, v in expected.items()):
        raise ValueError("external manifest differs from the registered scalar x86-64 proof")
    paths = {str(path.relative_to(root)): path for path in source_paths(root)}
    sources = manifest.get("source_sha256")
    if not isinstance(sources, dict) or set(sources) != set(paths):
        raise ValueError("external x86-64 semantic closure path set differs")
    for relative, path in paths.items():
        if source_digest(root, path) != sources[relative]:
            raise ValueError("external x86-64 semantic dependency differs: " + relative)
    dependencies = json.loads((root / "lake-manifest.json").read_text())
    scope = json.loads((root / "lean/verification-scope.json").read_text())
    if (manifest.get("external_dependencies") != dependencies or
            manifest.get("isa_model_commit") != scope["x86_64_isa_model"]["commit"] or
            manifest.get("standard_commit") != scope["standard"]["commit"]):
        raise ValueError("external x86-64 dependency metadata differs")


def checked_receipt(root, manifest, selected_hash, support, build_dir=None):
    if (support.get("supporting_checks") != "passed" or
            support.get("kernel_replay") != "fresh kernel; successful exit"):
        raise ValueError("complete supporting checks and fresh kernel replay are required")
    if not any(line.startswith(f"AXIOMS PASS {THEOREM}:") for line in support.get("axiom_audit", [])):
        raise ValueError("x86-64 equal axiom audit is missing")
    commit = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    if support.get("git_commit") != commit:
        raise ValueError("supporting evidence belongs to a different commit")
    for relative, digest in manifest["source_sha256"].items():
        if support.get("source_sha256", {}).get(relative) != digest:
            raise ValueError("supporting evidence differs from pinned x86-64 source: " + relative)
    artifacts = check_artifacts(build_dir or root / "build", root)
    if artifacts != support.get("x86_sha256_artifact_identity"):
        raise ValueError("x86-64 artifact identities differ from supporting evidence")
    return {"schema": 1, "function": "crypto_sha256", "proof_id": "equal", "isa": "x86_64",
            "theorem": THEOREM, "checked": True, "targets": TARGETS, "git_commit": commit,
            "expected_manifest_sha256": selected_hash,
            "expected_statement_sha256": hashlib.sha256(EXPECTED.encode()).hexdigest(),
            "source_sha256": manifest["source_sha256"], "artifacts": artifacts,
            "supporting_checks": "passed", "kernel_replay": support["kernel_replay"],
            "statement_comparison": "passed"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trusted-manifest", required=True, type=Path)
    parser.add_argument("--trusted-sha256", required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    output = root / "build/verification"
    receipt = output / RECEIPT
    receipt.unlink(missing_ok=True)
    manifest_path = args.trusted_manifest.resolve()
    if manifest_path.is_relative_to(root) or not re.fullmatch("[0-9a-f]{64}", args.trusted_sha256):
        raise ValueError("an externally selected manifest and SHA-256 are required")
    raw = manifest_path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != args.trusted_sha256:
        raise ValueError("expected x86-64 manifest does not match externally selected SHA-256")
    manifest = json.loads(raw)
    validate_sources(root, manifest)
    check_dependencies(root)
    expected_path = output / "ExternallyPinnedExpectedX86_64.lean"
    expected_path.write_text(manifest["expected_statement"])
    subprocess.run(["lake", "env", "lean", str(expected_path)], cwd=root, check=True)
    support = json.loads((output / "status.json").read_text())
    receipt.write_text(json.dumps(checked_receipt(root, manifest, args.trusted_sha256, support), indent=2) + "\n")
    print("Externally pinned scalar x86-64 SHA-256 statement and evidence matched.")


if __name__ == "__main__":
    main()
