#!/usr/bin/env python3
"""Check an externally selected expected statement and pinned semantic closure.

The caller MUST authenticate the reviewer and select the manifest/hash through
trusted policy outside candidate control. This utility cannot establish that
social/policy fact; it rejects the unapproved candidate package and has no
default trust root. It emits statement evidence, never a full verified mark.
Run the pinned dependency, axiom, fresh-kernel and artifact checks separately.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_lean_dependencies import check
from prepare_arm64_equal_review import EXPECTED, source_paths


def validate(root, manifest_path, selected_hash):
    root = root.resolve()
    manifest_path = manifest_path.resolve()
    if manifest_path.is_relative_to(root):
        raise ValueError("expected manifest must be supplied outside the candidate checkout")
    if not re.fullmatch("[0-9a-f]{64}", selected_hash):
        raise ValueError("an externally selected SHA-256 is required")
    raw = manifest_path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != selected_hash:
        raise ValueError("expected manifest does not match externally selected SHA-256")
    manifest = json.loads(raw)
    if manifest.get("schema") != 1:
        raise ValueError("unsupported expected-manifest schema")
    if manifest.get("theorem") != "Crypto.ARM64.sha256.equal":
        raise ValueError("expected manifest must identify the registered ARM64 SHA-256 equal theorem")
    review = manifest.get("review")
    if not isinstance(review, dict) or not all(
            isinstance(review.get(key), str) and review[key].strip()
            for key in ("reviewer", "immutable_source", "approved_utc")):
        raise ValueError("independent review identity, immutable source and approval date are required")
    expected_paths = {str(p.relative_to(root)) for p in source_paths(root)}
    if set(manifest.get("source_sha256", {})) != expected_paths:
        raise ValueError("expected semantic closure path set differs from the candidate")
    for relative, digest in manifest["source_sha256"].items():
        path = (root / relative).resolve()
        if not path.is_relative_to(root) or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError("expected semantic dependency differs: " + relative)
    check(root)
    statement = manifest.get("expected_statement")
    if not isinstance(statement, str) or not statement.strip():
        raise ValueError("trusted expected statement is missing")
    if statement != EXPECTED:
        raise ValueError("expected statement must compare the registered theorem against its full pinned baseline type")
    return manifest, statement


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trusted-manifest", required=True, type=Path)
    parser.add_argument("--trusted-sha256", required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    manifest, statement = validate(root, args.trusted_manifest, args.trusted_sha256)
    output = root / "build/verification"
    output.mkdir(parents=True, exist_ok=True)
    expected_path = output / "ExternallyPinnedExpected.lean"
    expected_path.write_text(statement)
    subprocess.run(["lake", "env", "lean", str(expected_path)], cwd=root, check=True)
    evidence = {"theorem": manifest["theorem"], "expected_manifest_sha256": args.trusted_sha256,
                "review": manifest["review"], "statement_comparison": "passed",
                "full_verified_mark": False,
                "scope": "Statement and semantic-closure evidence only; trusted external invocation/policy, axiom audit, fresh kernel and artifact/profile checks are separately required."}
    (output / "equal-statement-pin.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print("Externally pinned expected statement and semantic closure matched.")


if __name__ == "__main__":
    main()
