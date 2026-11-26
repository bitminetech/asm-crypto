#!/usr/bin/env python3
"""Verify x86-64 technical evidence using the trusted default branch and external pin."""
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_arm64_equal_bootstrap import load_module, safe_sources
from prepare_arm64_equal_review import source_digest


def validate(root, evidence, build, encoded, selected_hash):
    root = root.resolve()
    if not re.fullmatch("[0-9a-f]{64}", selected_hash):
        raise ValueError("externally selected x86-64 manifest SHA-256 is required")
    raw = base64.b64decode(encoded, validate=True)
    if hashlib.sha256(raw).hexdigest() != selected_hash:
        raise ValueError("external x86-64 manifest SHA-256 differs")
    manifest = json.loads(raw)
    if manifest.get("theorem") != "Crypto.X86_64.sha256.equal":
        raise ValueError("external manifest must identify x86-64 SHA-256 equal")
    # Use the trusted normalizer and authenticate every candidate source before
    # loading its technical receipt generator. No candidate bytecode is used.
    sources = safe_sources(root, manifest)
    for relative, digest in sources.items():
        if source_digest(root, root / relative) != digest:
            raise ValueError("external x86-64 semantic source differs: " + relative)
    modules = ("prepare_arm64_equal_review", "check_lean_dependencies", "check_arm64_artifacts",
               "prepare_x86_64_equal_review", "check_x86_sha256_artifacts", "check_x86_64_equal_pin")
    for name in modules:
        relative = f"tests/runner/{name}.py"
        path = root / relative
        if hashlib.sha256(path.read_bytes()).hexdigest() != sources.get(relative):
            raise ValueError("x86-64 bootstrap validator source differs: " + relative)
        checker = load_module(name, path)
    checker.validate_sources(root, manifest)
    support = json.loads((evidence / "status.json").read_text())
    receipt = json.loads((evidence / checker.RECEIPT).read_text())
    if receipt != checker.checked_receipt(root, manifest, selected_hash, support, build_dir=build):
        raise ValueError("CI technical receipt differs from completed pinned x86-64 proof evidence")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", required=True, type=Path)
    parser.add_argument("--evidence", required=True, type=Path)
    parser.add_argument("--build", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    args.output.unlink(missing_ok=True)
    receipt = validate(args.candidate, args.evidence, args.build, os.environ.get("EXPECTED_MANIFEST_B64", ""),
                       os.environ.get("EXPECTED_MANIFEST_SHA256", ""))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print("Pinned x86-64 SHA-256 sources, evidence and exact artifacts matched.")


if __name__ == "__main__":
    main()
