#!/usr/bin/env python3
"""Check an externally selected expected statement and pinned semantic closure.

Independent review and selection of the manifest/hash MUST occur through
trusted policy outside candidate control. This utility cannot establish that
policy fact and has no default trust root. It records only technical evidence,
without personal statements, identities or approval attestations.
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
from prepare_arm64_equal_review import EXPECTED, source_digest, source_paths


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
    expected_paths = {str(p.relative_to(root)) for p in source_paths(root)}
    if set(manifest.get("source_sha256", {})) != expected_paths:
        raise ValueError("expected semantic closure path set differs from the candidate")
    for relative, digest in manifest["source_sha256"].items():
        path = (root / relative).resolve()
        if not path.is_relative_to(root) or source_digest(root, path) != digest:
            raise ValueError("expected semantic dependency differs: " + relative)
    check(root)
    statement = manifest.get("expected_statement")
    if not isinstance(statement, str) or not statement.strip():
        raise ValueError("trusted expected statement is missing")
    if statement != EXPECTED:
        raise ValueError("expected statement must compare the registered theorem against its full pinned baseline type")
    return manifest, statement


def checked_receipt(root, manifest, selected_hash, support, build_dir=None):
    """Combine the statement gate with the completed proof/build evidence."""
    build_dir = root / "build" if build_dir is None else build_dir
    if support.get("supporting_checks") != "passed" or support.get("kernel_replay") != "fresh kernel; successful exit":
        raise ValueError("complete supporting checks and fresh kernel replay are required")
    if not any(line.startswith("AXIOMS PASS Crypto.ARM64.sha256.equal:") for line in support.get("axiom_audit", [])):
        raise ValueError("native equal axiom audit is missing")
    snapshot = support.get("source_sha256", {})
    for relative in manifest["source_sha256"]:
        path = root / relative
        if relative not in snapshot:
            raise ValueError("checked source snapshot is missing: " + relative)
        if source_digest(root, path) != snapshot[relative]:
            raise ValueError("supporting evidence is stale: " + relative)
    artifacts = support.get("arm64_artifact_identity", {}).get("artifacts", [])
    targets = ["linux-arm64", "windows-arm64", "macos-arm64"]
    if sorted(a.get("target", "") for a in artifacts) != sorted(targets):
        raise ValueError("all three exact ARM64 artifacts are required")
    for artifact in artifacts:
        if artifact.get("object_unwind_checked") is not True or artifact.get("metadata_relocations_checked") is not True:
            raise ValueError("artifact unwind/relocation validation is missing")
        for name in ("object_sha256", "archive_sha256", "text_sha256"):
            if not re.fullmatch("[0-9a-f]{64}", artifact.get(name, "")):
                raise ValueError("artifact digest is missing: " + name)
        directory = build_dir / artifact["target"]
        for name, filename in (("object_sha256", "sha256.o"), ("archive_sha256", "libasm-crypto.a")):
            if hashlib.sha256((directory / filename).read_bytes()).hexdigest() != artifact[name]:
                raise ValueError("checked artifact bytes are stale: " + artifact["target"] + "/" + filename)
    return {"schema": 1, "function": "crypto_sha256", "proof_id": "equal", "isa": "arm64",
            "theorem": "Crypto.ARM64.sha256.equal", "checked": True, "targets": targets,
            "expected_manifest_sha256": selected_hash,
            "expected_statement_sha256": hashlib.sha256(EXPECTED.encode()).hexdigest(),
            "source_sha256": manifest["source_sha256"], "artifacts": artifacts,
            "supporting_checks": "passed", "kernel_replay": support["kernel_replay"],
            "statement_comparison": "passed", "git_commit": support["git_commit"],
            "scope": "Recorded ARM64 library artifacts under explicit caller, ISA, memory, ABI, scheduling, timing and runtime-binding profile assumptions; no other ISA or consuming application claim."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trusted-manifest", required=True, type=Path)
    parser.add_argument("--trusted-sha256", required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    output = root / "build/verification"
    for name in ("checked-equal.json", "equal-statement-pin.json"):
        (output / name).unlink(missing_ok=True)
    manifest, statement = validate(root, args.trusted_manifest, args.trusted_sha256)
    output.mkdir(parents=True, exist_ok=True)
    expected_path = output / "ExternallyPinnedExpected.lean"
    expected_path.write_text(statement)
    subprocess.run(["lake", "env", "lean", str(expected_path)], cwd=root, check=True)
    evidence = {"theorem": manifest["theorem"], "expected_manifest_sha256": args.trusted_sha256,
                "statement_comparison": "passed",
                "full_verified_mark": False,
                "scope": "Statement and semantic-closure evidence only; trusted external invocation/policy, axiom audit, fresh kernel and artifact/profile checks are separately required."}
    (output / "equal-statement-pin.json").write_text(json.dumps(evidence, indent=2) + "\n")
    support = json.loads((output / "status.json").read_text())
    receipt = checked_receipt(root, manifest, args.trusted_sha256, support)
    (output / "checked-equal.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("Externally pinned expected statement and semantic closure matched.")


if __name__ == "__main__":
    main()
