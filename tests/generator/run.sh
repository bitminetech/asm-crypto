#!/bin/sh
# Generate the Keccak-256, HMAC, HKDF, AES, secp256k1, ChaCha20-Poly1305,
# X25519, P-256, SHA-512 and Ed25519 vectors inside the image from platform/linux/Dockerfile.
# Usage: tests/generator/run.sh OUT_DIR    (OUT_DIR must be outside this repo)
#
# OUT_DIR keeps the downloads (sources/), the libsecp256k1 build and the
# Python environment (.venv/), so a second run downloads and builds nothing again.
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
mkdir -p "$1"
out=$(cd "$1" && pwd)
case "$out/" in
  "$root"/*) echo "run.sh: $out is inside the repo; vectors are stored outside it" >&2; exit 2 ;;
esac

docker build -q -t asm-crypto-build -f "$root/platform/linux/Dockerfile" "$root/platform/linux" >/dev/null
docker run --rm -v "$root:/src:ro" -v "$out:/out" asm-crypto-build sh -eu -c '
    commit=6e2c8bc4ecdc6e71dbe7a368f360d8d453ce435d    # bitcoin-core/secp256k1 v0.8.0
    secp=/out/sources/secp256k1
    if [ "$(git -C $secp rev-parse HEAD 2>/dev/null)" != "$commit" ]; then
        rm -rf $secp /out/sources/secp256k1-build
        git init -q $secp
        git -C $secp fetch -q --depth 1 https://github.com/bitcoin-core/secp256k1 $commit
        git -C $secp checkout -q FETCH_HEAD
    fi
    if [ ! -f /out/sources/secp256k1-build/lib/libsecp256k1.so ]; then
        cmake -S $secp -B /out/sources/secp256k1-build -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=ON \
            -DSECP256K1_ENABLE_MODULE_ECDH=ON -DSECP256K1_BUILD_TESTS=OFF \
            -DSECP256K1_BUILD_EXHAUSTIVE_TESTS=OFF -DSECP256K1_BUILD_BENCHMARK=OFF >/dev/null
        cmake --build /out/sources/secp256k1-build -j >/dev/null
    fi
    [ -x /out/.venv/bin/python ] || python3 -m venv /out/.venv
    /out/.venv/bin/pip install -q --disable-pip-version-check --require-hashes -r tests/generator/requirements.txt
    SECP256K1_LIBRARY=/out/sources/secp256k1-build/lib/libsecp256k1.so \
        /out/.venv/bin/python -I tests/generator/primitives.py /out
'
