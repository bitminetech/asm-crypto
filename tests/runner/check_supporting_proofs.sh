#!/bin/sh
# This checks supporting lemmas, not the full equal baseline. No verified mark
# is produced. Run with Lean 4.29.1 on PATH after `lake update` / cache setup.
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
vectors=${1:?usage: check_supporting_proofs.sh VECTOR_DIRECTORY}
case "$(lean --version)" in
  'Lean (version 4.29.1,'*) ;;
  *) echo 'Expected pinned Lean 4.29.1' >&2; exit 1 ;;
esac
mkdir -p build/verification
rm -f build/verification/status.json
python3 -I tests/runner/check_lean_dependencies.py > build/verification/dependencies.json
lake build Reference Proofs reference-vectors arm64-model-check
.lake/build/bin/arm64-model-check > build/verification/arm64-model-check.log
python3 -I tests/runner/test_reference_vectors.py "$vectors"
lake env lean tests/runner/lean/CheckProofs.lean > build/verification/axioms.log
python3 -I tests/runner/test_proof_audit.py
lake env leanchecker --fresh Proofs > build/verification/kernel.log 2>&1
python3 -I tests/runner/check_arm64_artifacts.py > build/verification/arm64-artifacts.json
python3 -I tests/runner/test_arm64_artifacts.py
.lake/build/bin/reference-vectors \
    "$vectors/cavp-short.bin" "$vectors/cavp-long.bin" "$vectors/boundary.bin" \
    "$vectors/acvp-aft.bin" "$vectors/cavp-monte.bin" "$vectors/acvp-mct.bin" \
    "$vectors/acvp-ldt.bin" > build/verification/reference-vectors.log
python3 -I tests/runner/report_supporting_proofs.py
echo 'Supporting proof checks passed. Full equal and whole-library verification remain incomplete.'
