#!/usr/bin/env python3
"""Record successful supporting checks, explicitly excluding a checked equal."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prepare_arm64_equal_review import source_paths as pinned_source_paths, source_digest


def main():
    root = Path(__file__).resolve().parents[2]
    output = root / "build/verification"
    source_paths = sorted(set(pinned_source_paths(root) +
        [p for p in (root / "lean").rglob("*.lean") if "Imports" not in p.relative_to(root / "lean").parts]
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
    source_hashes = {str(p.relative_to(root)): source_digest(root, p)
                     for p in source_paths}
    scope = json.loads((root / "lean/verification-scope.json").read_text())
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
        "arm64_model_checks": (output / "arm64-model-check.log").read_text().splitlines(),
        "arm64_artifact_identity": json.loads((output / "arm64-artifacts.json").read_text()),
        "equal_status": scope["equal"]["status"],
        "candidate_equal": scope["equal"].get("candidate"),
        "independent_expected_statement_check": "not performed by the supporting-check job",
        "checked_equal_targets": [],
        "fully_verified_library": False,
        "scope": "lean/verification-scope.json"
    }
    (output / "status.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
