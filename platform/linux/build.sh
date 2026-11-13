#!/bin/sh
# Build the asm-crypto library and the test runner for one Linux ISA.
# Usage: platform/linux/build.sh ISA OUT_DIR    (ISA: x86_64, arm64 or riscv64)
# Runs inside the image from platform/linux/Dockerfile.
set -eu
isa=$1
out=$2
root=$(cd "$(dirname "$0")/../.." && pwd)

case "$isa" in
  x86_64)  target=x86_64-linux-gnu;  march="-march=x86-64" ;;
  arm64)   target=aarch64-linux-gnu; march="-march=armv8-a" ;;
  riscv64) target=riscv64-linux-gnu; march="-march=rv64gc -mabi=lp64d" ;;
  *) echo "unknown ISA: $isa" >&2; exit 2 ;;
esac

mkdir -p "$out"
objects=""
for name in sha256 keccak hmac aes secp256k1 chacha20 x25519 p256; do
    clang --target=$target $march -I"$root/include" -I"$root/platform/linux" \
        -c "$root/asm/core/$isa/$name.s" -o "$out/$name.o"
    objects="$objects $out/$name.o"
done
rm -f "$out/libasm-crypto.a"
llvm-ar rcs "$out/libasm-crypto.a" $objects

# Test runner (C), linked statically so QEMU user mode needs no target libraries.
clang --target=$target $march -std=c11 -O2 -Wall -Wextra -Werror -static -fuse-ld=lld \
    "$root/tests/runner/runner.c" -I"$root/platform/linux" "$root/tests/runner/abi_$isa.s" "$out/libasm-crypto.a" -o "$out/runner"
