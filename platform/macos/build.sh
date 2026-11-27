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
for name in sha256 keccak hmac aes secp256k1 chacha20 x25519 p256 sha512 ed25519 bls12381; do
    clang --target=$target -I"$root/include" -I"$root/platform/macos" \
        -c "$root/asm/core/$isa/$name.s" -o "$out/$name.o"
    objects="$objects $out/$name.o"
done
rm -f "$out/libasm-crypto.a"
llvm-ar --format=darwin rcs "$out/libasm-crypto.a" $objects

# The sha variant (sha-256.md, The sha variant): sha256x.s in place of sha256.s.
clang --target=$target -I"$root/include" -I"$root/platform/macos" \
    -c "$root/asm/core/$isa/sha256x.s" -o "$out/sha256x.o"
xobjects=$(echo "$objects" | sed "s#$out/sha256\.o#$out/sha256x.o#")
if [ "$isa" = x86_64 ]; then   # and bls12381x.s (bls12-381.md, The x variant): mulx, adcx and adox
    clang --target=$target -I"$root/include" -I"$root/platform/macos" -I"$root/asm/core/$isa" \
        -c "$root/asm/core/$isa/bls12381x.s" -o "$out/bls12381x.o"
    xobjects=$(echo "$xobjects" | sed "s#$out/bls12381\.o#$out/bls12381x.o#")
fi
rm -f "$out/libasm-crypto-sha.a"
llvm-ar --format=darwin rcs "$out/libasm-crypto-sha.a" $xobjects
