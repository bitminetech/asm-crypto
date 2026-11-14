#!/bin/sh
# Build the asm-crypto library and the test runner for one Windows ISA.
# Usage: platform/windows/build.sh ISA OUT_DIR    (ISA: x86_64 or arm64)
# Runs inside the image from platform/linux/Dockerfile. The library uses the
# pinned LLVM; the test runner uses llvm-mingw for the Windows C runtime.
set -eu
isa=$1
out=$2
root=$(cd "$(dirname "$0")/../.." && pwd)

case "$isa" in
  x86_64) target=x86_64-w64-windows-gnu;  march="-march=x86-64"; mingw=x86_64-w64-mingw32 ;;
  arm64)  target=aarch64-w64-windows-gnu; march="-march=armv8-a"; mingw=aarch64-w64-mingw32 ;;
  *) echo "unknown ISA: $isa" >&2; exit 2 ;;
esac

mkdir -p "$out"
objects=""
for name in sha256 keccak hmac aes secp256k1 chacha20 x25519 p256 sha512 ed25519; do
    clang --target=$target $march -I"$root/include" -I"$root/platform/windows" \
        -c "$root/asm/core/$isa/$name.s" -o "$out/$name.o"
    objects="$objects $out/$name.o"
done
rm -f "$out/libasm-crypto.a"
llvm-ar rcs "$out/libasm-crypto.a" $objects

/opt/llvm-mingw/bin/$mingw-clang $march -std=c11 -O2 -Wall -Wextra -Werror -static \
    "$root/tests/runner/runner.c" -I"$root/platform/windows" "$root/tests/runner/abi_$isa.s" "$out/libasm-crypto.a" -o "$out/runner.exe"
