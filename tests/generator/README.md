# Vector generation

```bash
python3 -I tests/generator/generate.py ~/.cache/asm-crypto/vectors
```

The script downloads the pinned NIST vectors, checks their SHA-256 pins, and writes binary case files to the output folder. The output folder must be outside this repo. The script also writes `manifest.txt`, which lists each file, its case count and its SHA-256.

| File | Source | Cases |
|---|---|---|
| `acvp-aft.bin` | NIST ACVP SHA2-256 1.0, functional tests | Messages of 215 to 1518 bytes |
| `acvp-mct.bin` | NIST ACVP SHA2-256 1.0, Monte Carlo test (alternate) | One seed, 100 digests |
| `acvp-ldt.bin` | NIST ACVP SHA2-256 1.0, large data tests | Messages of 1, 2, 4 and 8 GiB |
| `cavp-short.bin` | NIST CAVP `SHA256ShortMsg.rsp` | Messages of 0 to 64 bytes |
| `cavp-long.bin` | NIST CAVP `SHA256LongMsg.rsp` | Messages of 163 to 6400 bytes |
| `cavp-monte.bin` | NIST CAVP `SHA256Monte.rsp` | One seed, 100 digests |
| `boundary.bin` | Python `hashlib.sha256` | Every length from 0 to 512 bytes |

## File format

All numbers are unsigned 8-byte little-endian integers.

Each file starts with the 8 bytes `SHA256V1`, then `kind`, then the number of cases. The cases follow.

| `kind` | One case |
|---|---|
| 1, message | `length`, then `length` message bytes, then the 32-byte digest. |
| 2, Monte Carlo | `variant`, then `seed length`, then the seed bytes, then `count`, then `count` digests of 32 bytes. `variant` 1 is the CAVP SHAVS Monte test and `variant` 2 is the ACVP alternate Monte Carlo test. |
| 3, large message | `content length`, then the content bytes, then `full length`, then the 32-byte digest. The message is the content repeated to `full length` bytes. |
