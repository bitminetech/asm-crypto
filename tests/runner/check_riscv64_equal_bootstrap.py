#!/usr/bin/env python3
"""Validate Linux RV64GC proof evidence with the default branch's trusted tools."""
import argparse
import json
import os
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from read_equal_manifest import decode
from check_riscv64_equal_pin import RECEIPT, checked_receipt, validate_manifest


def validate(root, evidence, build, encoded, selected_hash):
    if not encoded or not selected_hash:
        raise ValueError("externally selected RV64 manifest and hash are required")
    manifest = validate_manifest(root, decode(encoded), selected_hash)
    support = json.loads((evidence / "riscv64-status.json").read_text())
    receipt = json.loads((evidence / RECEIPT).read_text())
    if receipt != checked_receipt(root, manifest, selected_hash, support, build):
        raise ValueError("RV64 receipt differs from the pinned CI evidence")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("candidate", "evidence", "build", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    output.unlink(missing_ok=True)
    receipt = validate(args.candidate.resolve(), args.evidence.resolve(), args.build.resolve(),
                       os.environ.get("EXPECTED_MANIFEST_B64", ""), os.environ.get("EXPECTED_MANIFEST_SHA256", ""))
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print("Pinned RV64 SHA-256 sources, CI evidence and exact artifacts matched.")


if __name__ == "__main__":
    main()
