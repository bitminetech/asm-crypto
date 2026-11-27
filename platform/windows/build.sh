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
for name in sha256 keccak hmac aes secp256k1 chacha20 x25519 p256 sha512 ed25519 bls12381; do
    clang --target=$target $march -I"$root/include" -I"$root/platform/windows" \
        -c "$root/asm/core/$isa/$name.s" -o "$out/$name.o"
    objects="$objects $out/$name.o"
done
rm -f "$out/libasm-crypto.a"
llvm-ar rcs "$out/libasm-crypto.a" $objects

/opt/llvm-mingw/bin/$mingw-clang $march -std=c11 -O2 -Wall -Wextra -Werror -static \
    "$root/tests/runner/runner.c" -I"$root/platform/windows" "$root/tests/runner/abi_$isa.s" "$out/libasm-crypto.a" -o "$out/runner.exe"

# The sha variant (sha-256.md, The sha variant): sha256x.s in place of sha256.s, and its runner.
clang --target=$target $march -I"$root/include" -I"$root/platform/windows" \
    -c "$root/asm/core/$isa/sha256x.s" -o "$out/sha256x.o"
xobjects=$(echo "$objects" | sed "s#$out/sha256\.o#$out/sha256x.o#")
if [ "$isa" = x86_64 ]; then   # and bls12381x.s (bls12-381.md, The x variant): mulx, adcx and adox
    clang --target=$target $march -I"$root/include" -I"$root/platform/windows" -I"$root/asm/core/$isa" \
        -c "$root/asm/core/$isa/bls12381x.s" -o "$out/bls12381x.o"
    xobjects=$(echo "$xobjects" | sed "s#$out/bls12381\.o#$out/bls12381x.o#")
fi
rm -f "$out/libasm-crypto-sha.a"
llvm-ar rcs "$out/libasm-crypto-sha.a" $xobjects
/opt/llvm-mingw/bin/$mingw-clang $march -std=c11 -O2 -Wall -Wextra -Werror -static -DCRYPTO_SHA_VARIANT \
    "$root/tests/runner/runner.c" -I"$root/platform/windows" "$root/tests/runner/abi_$isa.s" "$out/libasm-crypto-sha.a" -o "$out/runner-sha.exe"
