#!/bin/sh
# Run with the pinned Lean toolchain and all three Linux runners.
set -eu
cd "$(dirname "$0")/../.."
output=build/verification
mkdir -p "$output"
rm -f "$output/hmac-sha256-status.json" "$output/checked-equal-hmac-sha256.json"
python3 -I tests/runner/check_lean_dependencies.py > "$output/hmac-sha256-dependencies.json"
lake build +Proofs.HMACSHA256:olean
lake env lean tests/runner/lean/CheckHmacSHA256.lean > "$output/hmac-sha256-axioms.log"
for module in ARM64Equal X86Equal RISCV64Equal ARM64Reserved RISCV64Reserved; do
    echo "Replaying Proofs.HMACSHA256.$module in a fresh kernel"
    lake env leanchecker --fresh "Proofs.HMACSHA256.$module" \
        > "$output/hmac-sha256-kernel-$module.log" 2>&1
done
python3 -I tests/runner/hmac_equal.py report
