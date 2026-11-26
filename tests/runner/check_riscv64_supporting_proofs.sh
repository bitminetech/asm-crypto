#!/bin/sh
# Run with the CI-installed Lean toolchain and Linux RV64 build artifacts.
set -eu
cd "$(dirname "$0")/../.."
mkdir -p build/verification
rm -f build/verification/riscv64-status.json build/verification/checked-equal-riscv64.json
python3 -I tests/runner/check_lean_dependencies.py > build/verification/riscv64-dependencies.json
lake build +Proofs.RISCV64:olean
lake env lean tests/runner/lean/CheckRISCV64.lean > build/verification/riscv64-axioms.log
lake env leanchecker --fresh Proofs.RISCV64 > build/verification/riscv64-kernel.log 2>&1
python3 -I tests/runner/check_riscv64_sha256_artifacts.py > build/verification/riscv64-artifacts.json
python3 -I - <<'PY'
import json
from pathlib import Path
import subprocess
import sys

root = Path.cwd().resolve()
sys.path.insert(0, str(root / "tests/runner"))
from prepare_riscv64_equal_review import source_hashes

output = root / "build/verification"
audit = (output / "riscv64-axioms.log").read_text().splitlines()
report = {
    "git_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
    "source_sha256": source_hashes(root),
    "supporting_checks": "passed",
    "kernel_replay": "fresh kernel; successful exit",
    "axiom_audit": [line[line.index("AXIOMS PASS "):] for line in audit if "AXIOMS PASS " in line],
    "artifact": json.loads((output / "riscv64-artifacts.json").read_text()),
}
(output / "riscv64-status.json").write_text(json.dumps(report, indent=2) + "\n")
PY
