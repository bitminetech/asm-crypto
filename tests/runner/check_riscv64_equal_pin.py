#!/usr/bin/env python3
"""Check the externally selected Linux RV64GC statement and exact build evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_lean_dependencies import check as check_dependencies
from check_riscv64_sha256_artifacts import check as check_artifacts
from prepare_riscv64_equal_review import EXPECTED, TARGETS, THEOREM, metadata, source_hashes

RECEIPT = "checked-equal-riscv64.json"
PROOF_CHECKS = {
    "supporting_checks": "passed",
    "kernel_replay": "fresh kernel; successful exit",
}


def validate_manifest(root, raw, selected_hash):
    if not re.fullmatch(r"[0-9a-f]{64}", selected_hash) or hashlib.sha256(raw).hexdigest() != selected_hash:
        raise ValueError("external RV64 manifest SHA-256 differs")
    manifest = json.loads(raw)
    if type(manifest) is not dict or type(manifest.get("schema")) is not int:
        raise ValueError("invalid external RV64 manifest schema")
    if any(manifest.get(key) != value for key, value in metadata(root).items()):
        raise ValueError("external manifest differs from the Linux RV64 SHA-256 statement or dependency pins")
    if manifest.get("source_sha256") != source_hashes(root):
        raise ValueError("external RV64 source closure differs")
    return manifest


def checked_receipt(root, manifest, selected_hash, support, build_dir):
    if any(support.get(key) != value for key, value in PROOF_CHECKS.items()):
        raise ValueError("supporting checks and fresh RV64 kernel replay are required")
    if not any(line.startswith(f"AXIOMS PASS {THEOREM}:") for line in support.get("axiom_audit", [])):
        raise ValueError("RV64 axiom audit is missing")
    commit = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    if support.get("git_commit") != commit or support.get("source_sha256") != manifest["source_sha256"]:
        raise ValueError("RV64 supporting evidence differs from the pinned candidate")
    artifacts = check_artifacts(build_dir, root=root)
    if artifacts != support.get("artifact"):
        raise ValueError("RV64 artifact differs from supporting evidence")
    return receipt_fields(commit, artifacts, manifest["source_sha256"], selected_hash)


def receipt_fields(commit, artifacts, sources, selected_hash):
    return {
        **PROOF_CHECKS, "schema": 1, "function": "crypto_sha256", "proof_id": "equal",
        "isa": "riscv64", "targets": TARGETS, "theorem": THEOREM, "checked": True,
        "git_commit": commit, "expected_manifest_sha256": selected_hash,
        "expected_statement_sha256": hashlib.sha256(EXPECTED.encode()).hexdigest(),
        "source_sha256": sources, "artifacts": artifacts, "statement_comparison": "passed",
    }


def validate_receipt(root, build_dir, receipt):
    if type(receipt) is not dict or type(receipt.get("schema")) is not int or receipt.get("checked") is not True:
        raise ValueError("RV64 receipt is not checked schema 1")
    digest = receipt.get("expected_manifest_sha256")
    if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise ValueError("RV64 receipt lacks the selected external pin")
    commit = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    artifacts = check_artifacts(build_dir, root=root)
    if receipt != receipt_fields(commit, artifacts, source_hashes(root), digest):
        raise ValueError("RV64 receipt differs from the current statement, source or artifact")
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trusted-manifest", required=True, type=Path)
    parser.add_argument("--trusted-sha256", required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    output = root / "build/verification"
    receipt = output / RECEIPT
    receipt.unlink(missing_ok=True)
    path = args.trusted_manifest.resolve()
    if path.is_relative_to(root):
        raise ValueError("the RV64 pin must be supplied outside the candidate checkout")
    manifest = validate_manifest(root, path.read_bytes(), args.trusted_sha256)
    check_dependencies(root)
    expected = output / "ExternallyPinnedExpectedRISCV64.lean"
    expected.write_text(manifest["expected_statement"])
    subprocess.run(["lake", "env", "lean", str(expected)], cwd=root, check=True)
    support = json.loads((output / "riscv64-status.json").read_text())
    checked = checked_receipt(root, manifest, args.trusted_sha256, support, root / "build")
    receipt.write_text(json.dumps(checked, indent=2) + "\n")
    print("Externally pinned RV64 SHA-256 statement and evidence matched.")


if __name__ == "__main__":
    main()
