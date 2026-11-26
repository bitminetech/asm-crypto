#!/usr/bin/env python3
"""Prepare the Linux RV64GC SHA-256 statement and source closure for independent selection."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prepare_arm64_equal_review import source_digest, source_paths as shared_source_paths

THEOREM = "Crypto.RISCV64.modeled_baseline"
TARGETS = ["linux-riscv64"]
EXPECTED = f"""import Proofs.RISCV64

example : Crypto.Baseline.Stateless.Equal Crypto.RISCV64.modeledRequirements :=
  {THEOREM}
"""


def source_paths(root):
    paths = set(shared_source_paths(root)) | set((root / "asm/core/riscv64").rglob("*.s"))
    if any(path.is_symlink() or not path.resolve().is_relative_to(root) for path in paths):
        raise ValueError("reviewed proof and build sources must be regular files inside the checkout")
    return sorted(paths)


def source_hashes(root):
    return {path.relative_to(root).as_posix(): source_digest(root, path) for path in source_paths(root)}


def metadata(root):
    scope = json.loads((root / "lean/verification-scope.json").read_text())
    gitlink = subprocess.check_output([
        "git", "-C", str(root), "ls-tree", "HEAD", "lean/Imports/arm64",
    ], text=True).split()
    if len(gitlink) != 4 or gitlink[:2] != ["160000", "commit"]:
        raise ValueError("RV64 requires the pinned ARM64 memory source gitlink")
    return {
        "schema": 1,
        "function": "crypto_sha256",
        "proof_id": "equal",
        "isa": "riscv64",
        "profile": "scalar RV64GC, Linux, LP64D",
        "targets": TARGETS,
        "theorem": THEOREM,
        "expected_statement": EXPECTED,
        "external_dependencies": json.loads((root / "lake-manifest.json").read_text()),
        "arm64_memory_dependency_commit": gitlink[2],
        "standard_commit": scope["riscv64_isa_model"]["standard_commit"],
    }


def main():
    root = Path(__file__).resolve().parents[2]
    output = root / "build/verification/riscv64-equal-review"
    output.mkdir(parents=True, exist_ok=True)
    manifest = {**metadata(root), "source_sha256": source_hashes(root)}
    data = (json.dumps(manifest, separators=(",", ":"), sort_keys=True) + "\n").encode()
    (output / "Expected.lean").write_text(EXPECTED)
    (output / "manifest.json").write_bytes(data)
    print("Candidate manifest SHA-256: " + hashlib.sha256(data).hexdigest())


if __name__ == "__main__":
    main()
