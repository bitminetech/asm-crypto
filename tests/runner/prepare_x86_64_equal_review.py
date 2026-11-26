#!/usr/bin/env python3
"""Prepare the scalar x86-64 SHA-256 statement and source closure for review."""
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prepare_arm64_equal_review import source_digest, source_paths as shared_source_paths


THEOREM = "Crypto.X86_64.sha256.equal"
EXPECTED = f"""import Proofs

example : Crypto.Baseline.Stateless.Equal Crypto.X86_64.NativeRequirements.requirements :=
  {THEOREM}
"""


def source_paths(root):
    paths = set(shared_source_paths(root)) | set((root / "asm/core/x86_64").rglob("*.s"))
    if any(path.is_symlink() or not path.resolve().is_relative_to(root) for path in paths):
        raise ValueError("reviewed proof and build sources must be regular files inside the checkout")
    return sorted(paths)


def main():
    root = Path(__file__).resolve().parents[2]
    output = root / "build/verification/x86-64-equal-review"
    output.mkdir(parents=True, exist_ok=True)
    scope = json.loads((root / "lean/verification-scope.json").read_text())
    manifest = {
        "schema": 1,
        "function": "crypto_sha256",
        "proof_id": "equal",
        "isa": "x86-64",
        "profile": "scalar baseline",
        "targets": ["linux-x86_64", "macos-x86_64", "windows-x86_64"],
        "theorem": THEOREM,
        "expected_statement": EXPECTED,
        "source_sha256": {str(path.relative_to(root)): source_digest(root, path) for path in source_paths(root)},
        "external_dependencies": json.loads((root / "lake-manifest.json").read_text()),
        "isa_model_commit": scope["x86_64_isa_model"]["commit"],
        "standard_commit": scope["standard"]["commit"],
    }
    data = (json.dumps(manifest, separators=(",", ":"), sort_keys=True) + "\n").encode()
    (output / "Expected.lean").write_text(EXPECTED)
    (output / "manifest.json").write_bytes(data)
    print("Candidate manifest SHA-256: " + hashlib.sha256(data).hexdigest())


if __name__ == "__main__":
    main()
