#!/usr/bin/env python3
"""Prepare candidate evidence for independent §8 review; never approve it.

The reviewer must inspect the expected type and its semantic dependencies,
approve an immutable manifest, and select its hash through policy outside the
candidate repository. A generated package or a local agent review is not that
approval. All local Lean sources are conservatively pinned, including proofs.
"""
import hashlib
import json
from pathlib import Path


EXPECTED = """import Proofs

example : Crypto.Baseline.Stateless.Equal Crypto.ARM64.NativeRequirements.requirements :=
  Crypto.ARM64.sha256.equal
"""


def source_paths(root):
    return sorted(
        [p for p in (root / "lean").rglob("*.lean")
         if "Imports" not in p.relative_to(root / "lean").parts]
        + list((root / "include").rglob("*.inc"))
        + list((root / "asm/core/arm64").rglob("*.s"))
        + list((root / "tests/runner").glob("*.py"))
        + list((root / "tests/runner").glob("*.sh"))
        + list((root / "tests/runner/lean").glob("*.lean"))
        + list((root / "docs/models").glob("*.md"))
        + [p for p in (root / "platform").rglob("*") if p.is_file()]
        + [root / name for name in (
            "lakefile.toml", "lake-manifest.json", "lean-toolchain", ".gitmodules",
            "lean/Models/arm64-sha256.text.hex", "lean/verification-scope.json",
            "docs/reference/sha-256.md", "README.md", ".github/workflows/ci.yml")])


def main():
    root = Path(__file__).resolve().parents[2]
    output = root / "build/verification/arm64-equal-review"
    output.mkdir(parents=True, exist_ok=True)
    (output / "Expected.lean").write_text(EXPECTED)
    manifest = {
        "schema": 1,
        "claim": "ARM64 crypto_sha256 equal; candidate for independent review",
        "theorem": "Crypto.ARM64.sha256.equal",
        "expected_statement": EXPECTED,
        "review": None,
        "source_sha256": {
            str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in source_paths(root)},
        "external_dependencies": json.loads((root / "lake-manifest.json").read_text()),
        "isa_model_commit": "b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b",
        "standard_commit": json.loads((root / "lean/verification-scope.json").read_text())["standard"]["commit"],
        "policy": "Independent reviewer approves definitions/semantic closure, fills review identity and immutable source reference, and pins the final manifest hash outside candidate control. No checked mark is authorized by this generated file."
    }
    data = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()
    (output / "manifest.json").write_bytes(data)
    print("Candidate review manifest SHA-256: " + hashlib.sha256(data).hexdigest())
    print("Independent approval/policy selection remains required.")


if __name__ == "__main__":
    main()
