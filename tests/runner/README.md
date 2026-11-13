# Test runner

`runner.c` reads the binary case files from [tests/generator/](../generator/), calls the library for every case, and compares the results. It is test code in C; the library itself is pure assembly.

```bash
python3 -I tests/generator/generate.py ~/.cache/asm-crypto/vectors
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

Name vector files after the folder to run only those files, for example `tests/runner/docker.sh DIR cavp-short.bin`. With no names, every file runs, including the 1 to 8 GiB messages in `acvp-ldt.bin`.

[.github/workflows/ci.yml](../../.github/workflows/ci.yml) runs every file on all 7 targets: Linux on GitHub's x64 and ARM64 runners (RISC-V under QEMU), Windows on `windows-2025` and `windows-11-arm`, and macOS on `macos-15-intel` and `macos-15`.

The runner maps the large messages instead of storing them: it maps one 4 MiB block of repeated content again and again, so an 8 GiB message needs 8 GiB of address space but only 4 MiB of memory.

## Tick tables

- When every file runs, the runner prints `FUNCTION crypto_sha256 PASS` or `FUNCTION crypto_sha256 FAIL`.
- CI runs `tick_tables.py` after the tests of all 7 targets.
- An OS cell gets ✅ when the runner of that target printed `PASS`.
- ARM64 `equal` gets ✅ when its checked receipt matches the current sources and artifacts and vectors pass on all three ARM64 OS builds. Other ISA proof cells remain empty.
- On a push to `main`, CI commits the tables when they change.
