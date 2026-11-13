# Test runner

`runner.c` reads the binary case files from [tests/generator/](../generator/), calls the library for every case, and compares the results. It is test code in C; the library itself is pure assembly.

```bash
python3 -I tests/generator/generate.py ~/.cache/asm-crypto/vectors
```

```bash
tests/generator/run.sh ~/.cache/asm-crypto/vectors
```

```bash
tests/runner/docker.sh ~/.cache/asm-crypto/vectors
```

```bash
tests/runner/macos.sh ~/.cache/asm-crypto/vectors
```

| Script | What it does |
|---|---|
| `docker.sh` | Builds the Docker image, builds the library for all 7 targets into `build/`, and runs the vectors for Linux x86-64, ARM64 and RISC-V. ISAs other than the host's run under QEMU user mode. |
| `macos.sh` | Links the runner on a Mac against the library that `docker.sh` built, and runs the vectors. |
| `tick_tables.py` | Writes the tick table of each function into its document, from the results of every target. |
| `abi_x86_64.s`, `abi_arm64.s`, `abi_riscv64.s` | `abi_call`, through which the runner calls every library function. Test code in assembly. |

Name vector files after the folder to run only those files, for example `tests/runner/docker.sh DIR cavp-short.bin`. With no names, every file runs, including the 1 to 8 GiB messages in `acvp-ldt.bin`.

[.github/workflows/ci.yml](../../.github/workflows/ci.yml) runs every file on all 7 targets: Linux on GitHub's x64 and ARM64 runners (RISC-V under QEMU), Windows on `windows-2025` and `windows-11-arm`, and macOS on `macos-15-intel` and `macos-15`.

Inputs sit at an offset with unused room after them, and must stay unchanged. Fixed size outputs have guard bytes on both sides. Each `ByteList` output and scratch buffer gets exactly the size the function needs, with guard bytes after it; the runner also calls with one byte less, which must give `CRYPTO_BUFFER_TOO_SMALL`.

The runner maps the large messages instead of storing them: it maps one 4 MiB block of repeated content again and again, so an 8 GiB message needs 8 GiB of address space but only 4 MiB of memory.

## ABI and stack check

- The runner calls every L2 function through `abi_call`, in `abi_x86_64.s`, `abi_arm64.s` and `abi_riscv64.s`. It is test code in assembly.
- Before the call, `abi_call` sets each register that the callee must keep to a known value, and paints the stack below the call.
- After the call, it records the status, the kept state that changed, and the bytes of stack the call used.
- It then puts the stack pointer, the flags and the floating point control state back.
- The runner prints the most stack each function used, and fails when it is over the README cap of 4096 bytes, or when kept state changed.

| ISA | Kept state it checks |
|---|---|
| x86-64 | `rbx`, `rbp`, `r12` to `r15`, `rsp`, the direction flag, `mxcsr`, the x87 control word |
| ARM64 | `x19` to `x29`, `sp`, `d8` to `d15`, `fpcr` |
| RISC-V | `s0` to `s11`, `sp`, `fs0` to `fs11`, `gp`, `tp` |

A failure prints a mask with one bit for each changed item:

- x86-64: bits 0 to 5 are `rbx`, `rbp`, `r12`, `r13`, `r14` and `r15`. Bit 60 is the x87 control word, bit 61 `mxcsr`, bit 62 the direction flag and bit 63 `rsp`.
- ARM64: bits 0 to 9 are `x19` to `x28`, and bit 10 `x29`. Bits 11 to 18 are `d8` to `d15`. Bit 61 is `fpcr` and bit 63 `sp`.
- RISC-V: bits 0 to 11 are `s0` to `s11`, and bits 12 to 23 `fs0` to `fs11`. Bit 24 is `gp`, bit 25 `tp` and bit 63 `sp`.

The record that `abi_call` reads and writes:

| Offset | Field | Type | Meaning |
|---|---|---|---|
| 0 | `fn` | u64 | Address of the function to call |
| 8 | `arg` | 5 u64 | The arguments |
| 48 | `paint` | u64 | Bytes of stack to paint below the call, a multiple of 8 |
| 56 | `status` | u64 | The status the call returned |
| 64 | `fault` | u64 | The mask of kept state that changed |
| 72 | `stack` | u64 | Bytes of stack the call used |
| 80 | `scratch` | 32 bytes | Workspace for `abi_call` |

## Tick tables

- When every file runs, the runner prints `FUNCTION <name> PASS` or `FUNCTION <name> FAIL` for each L2 function.
- CI runs `tick_tables.py` after the tests of all 7 targets.
- An OS cell gets ✅ when the runner of that target printed `PASS`.
- ARM64 `equal` gets ✅ when its checked receipt matches the current sources and artifacts and vectors pass on all three ARM64 OS builds. Other ISA proof cells remain empty.
- On a push to `main`, CI commits the tables when they change.
