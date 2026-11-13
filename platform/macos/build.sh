#!/bin/sh
# Build the asm-crypto library for one macOS ISA.
# Usage: platform/macos/build.sh ISA OUT_DIR    (ISA: x86_64 or arm64)
# Runs inside the image from platform/linux/Dockerfile, so the library uses the
# pinned LLVM. The test runner needs the macOS SDK, so link-runner.sh links it
# on a Mac.
set -eu
isa=$1
out=$2
root=$(cd "$(dirname "$0")/../.." && pwd)

case "$isa" in
  x86_64) target=x86_64-apple-macos11 ;;
  arm64)  target=arm64-apple-macos11 ;;
  *) echo "unknown ISA: $isa" >&2; exit 2 ;;
esac

mkdir -p "$out"
objects=""
for name in sha256 keccak hmac aes secp256k1 chacha20 x25519 p256; do
    clang --target=$target -I"$root/include" -I"$root/platform/macos" \
        -c "$root/asm/core/$isa/$name.s" -o "$out/$name.o"
    objects="$objects $out/$name.o"
done
rm -f "$out/libasm-crypto.a"
llvm-ar --format=darwin rcs "$out/libasm-crypto.a" $objects
