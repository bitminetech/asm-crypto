#!/bin/sh
# Build every target in Docker, then run the vectors for the three Linux ISAs.
# Usage: tests/runner/docker.sh VECTOR_DIR [FILE ...]
#
# Outputs go to build/<os>-<isa>/. Linux ISAs other than the build host's own
# run under QEMU user mode. The Windows and macOS runners are run elsewhere:
# macOS ARM64 on a Mac (tests/runner/macos.sh), the rest in GitHub Actions.
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
vectors=$(cd "$1" && pwd)
shift
image=asm-crypto-build

docker build -q -t "$image" -f "$root/platform/linux/Dockerfile" "$root/platform/linux" >/dev/null
docker run --rm -v "$root:/src" -v "$vectors:/vectors:ro" "$image" sh -eu -c '
    platform/build-all.sh
    host=$(uname -m)
    status=0
    for isa in x86_64 arm64 riscv64; do
        case $isa in
          x86_64)  machine=x86_64;  qemu=qemu-x86_64 ;;
          arm64)   machine=aarch64; qemu=qemu-aarch64 ;;
          riscv64) machine=riscv64; qemu=qemu-riscv64 ;;
        esac
        [ "$machine" = "$host" ] && qemu=""
        echo "== linux $isa${qemu:+ (under $qemu)}"
        $qemu build/linux-$isa/runner /vectors "$@" || status=1
    done
    exit $status
' sh "$@"
