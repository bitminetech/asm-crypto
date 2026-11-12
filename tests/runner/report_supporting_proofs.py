#!/usr/bin/env python3
"""Record successful supporting checks, explicitly excluding a checked equal."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    root = Path(__file__).resolve().parents[2]
    output = root / "build/verification"
    source_paths = sorted(set(
        list((root / "lean").rglob("*.lean"))
        + list((root / "tests/runner").rglob("*.lean"))
        + list((root / "tests/runner").glob("*.py"))
        + list((root / "tests/runner").glob("*.sh"))
        + list((root / "asm/core").rglob("*.s"))
        + list((root / "include").rglob("*.inc"))
        + list((root / "docs/models").glob("*.md"))
        + [root / name for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain",
                                    "README.md", "docs/reference/sha-256.md",
                                    ".github/workflows/ci.yml",
                                    "lean/verification-scope.json", "lean/Models/arm64-sha256.text.hex")]))
    source_hashes = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                     for p in source_paths}
    report = {
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "git_commit": subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip(),
        "working_tree_modified": bool(subprocess.check_output(
            ["git", "-C", str(root), "status", "--porcelain"], text=True).strip()),
        "lean_version": subprocess.check_output(["lean", "--version"], text=True).strip(),
        "source_sha256": source_hashes,
        "supporting_checks": "passed",
        "axiom_audit": (output / "axioms.log").read_text().splitlines(),
        "kernel_replay": "fresh kernel; successful exit",
        "reference_vectors": (output / "reference-vectors.log").read_text().splitlines(),
        "arm64_artifact_identity": json.loads((output / "arm64-artifacts.json").read_text()),
        "equal_status": "in progress",
        "checked_equal_targets": [],
        "fully_verified_library": False,
        "scope": "lean/verification-scope.json"
    }
    (output / "status.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
