/*
 * SHA-256 vector runner for asm-crypto.
 *
 * Usage: runner VECTOR_DIR [FILE ...]
 *
 * Reads the binary case files that tests/generator/generate.py writes (format
 * in tests/generator/README.md), calls crypto_sha256 for every case and
 * compares the results. With no FILE arguments it runs every file. It exits
 * with status 0 only when every case of every file it ran passes.
 *
 * Besides the digest, each message case checks that the function returns 0,
 * reads the message from its offset, ignores the unused room, leaves the
 * message unchanged and writes nothing outside the 32 digest bytes.
 *
 * Every call goes through abi_call (tests/runner/abi_<ISA>.s). The runner
 * prints the most stack the function used, and fails when a call uses more
 * than the README cap or changes state that the ABI says it must keep.
 */
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#include <windows.h>
#else
#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>
#endif

/* C view of the interface in include/crypto.inc and docs/reference/sha-256.md. */
#if defined(_WIN32) && defined(__x86_64__)
#define CRYPTO_ABI __attribute__((sysv_abi))
#else
#define CRYPTO_ABI
#endif
CRYPTO_ABI uint64_t crypto_sha256(const void *message, void *digest);

/*
 * ABI and stack check. abi_call sets every register the callee must keep to a
 * known value and paints PAINT_BYTES of stack below the call. Afterwards it
 * reports the kept state that changed, and the bytes of stack the call used,
 * its return address included on x86-64. The layout of its record is in
 * tests/runner/README.md.
 */
#define STACK_CAP 1024 /* README: stack per call */
#define PAINT_BYTES (STACK_CAP + 1024)

typedef struct {
    uint64_t fn, arg[5], paint, status, fault, stack, scratch[4];
} abi_ctx;
CRYPTO_ABI void abi_call(abi_ctx *ctx);

static uint64_t stack_peak, abi_fault;

/* crypto_sha256(message, digest), through abi_call. */
static uint64_t sha256_checked(const void *message, void *digest) {
    abi_ctx c;
    memset(&c, 0, sizeof c);
    c.fn = (uint64_t)(uintptr_t)crypto_sha256;
    c.arg[0] = (uint64_t)(uintptr_t)message;
    c.arg[1] = (uint64_t)(uintptr_t)digest;
    c.paint = PAINT_BYTES;
    abi_call(&c);
    if (c.stack > stack_peak) stack_peak = c.stack;
    abi_fault |= c.fault;
    return c.status;
}

#define CRYPTO_OK 0
#define BYTES_FIXED 24
#define DIGEST 32

static const char *ALL_FILES[] = {
    "cavp-short.bin", "cavp-long.bin", "boundary.bin", "acvp-aft.bin",
    "cavp-monte.bin", "acvp-mct.bin", "acvp-ldt.bin",
};

static uint64_t rd64(const uint8_t *p) {
    uint64_t v = 0;
    for (int i = 7; i >= 0; i--) v = (v << 8) | p[i];
    return v;
}

static void wr64(uint8_t *p, uint64_t v) {
    for (int i = 0; i < 8; i++) p[i] = (uint8_t)(v >> (8 * i));
}

/* A cursor over one file, failing hard on a short read. */
typedef struct {
    const uint8_t *p;
    const uint8_t *end;
    const char *name;
} cursor;

static const uint8_t *take(cursor *c, uint64_t n) {
    if ((uint64_t)(c->end - c->p) < n) {
        fprintf(stderr, "%s: file ends early\n", c->name);
        exit(2);
    }
    const uint8_t *r = c->p;
    c->p += n;
    return r;
}

static uint64_t take64(cursor *c) { return rd64(take(c, 8)); }

/* Hash msg[0..len) through a fresh byte list value. Returns 1 when every check passes. */
static int hash_checked(const uint8_t *msg, uint64_t len, uint8_t md[DIGEST]) {
    const uint64_t offset = 32;      /* past the 24 fixed bytes, so the offset field matters */
    const uint64_t room = 7;         /* unused room after the bytes in use */
    uint64_t size = offset + len + room;
    uint8_t *buf = malloc((size_t)size);
    uint8_t *before = malloc((size_t)size);
    if (!buf || !before) {
        fprintf(stderr, "out of memory\n");
        exit(2);
    }
    memset(buf, 0xA5, (size_t)size);
    wr64(buf + 0, size);
    wr64(buf + 8, offset);
    wr64(buf + 16, len);
    if (len) memcpy(buf + offset, msg, (size_t)len);
    memcpy(before, buf, (size_t)size);

    uint64_t out[6];                 /* 8 guard bytes, 32 digest bytes, 8 guard bytes */
    uint8_t *o = (uint8_t *)out;
    memset(o, 0x5A, sizeof out);
    uint64_t status = sha256_checked(buf, o + 8);

    int ok = status == CRYPTO_OK && memcmp(buf, before, (size_t)size) == 0;
    for (int i = 0; i < 8; i++) ok &= o[i] == 0x5A && o[40 + i] == 0x5A;
    memcpy(md, o + 8, DIGEST);
    free(buf);
    free(before);
    return ok;
}

static int run_messages(cursor *c, uint64_t n) {
    int bad = 0;
    for (uint64_t k = 0; k < n; k++) {
        uint64_t len = take64(c);
        const uint8_t *msg = take(c, len);
        const uint8_t *want = take(c, DIGEST);
        uint8_t got[DIGEST];
        if (!hash_checked(msg, len, got) || memcmp(got, want, DIGEST) != 0) {
            if (bad < 5) fprintf(stderr, "%s: case %llu (length %llu) fails\n", c->name,
                                 (unsigned long long)k, (unsigned long long)len);
            bad++;
        }
    }
    return bad;
}

/* Monte Carlo tests: variant 1 is CAVP SHAVS, variant 2 is ACVP alternate. */
static int run_monte(cursor *c, uint64_t n) {
    int bad = 0;
    for (uint64_t k = 0; k < n; k++) {
        uint64_t variant = take64(c);
        uint64_t seed_len = take64(c);
        const uint8_t *seed0 = take(c, seed_len);
        uint64_t count = take64(c);
        const uint8_t *want = take(c, count * DIGEST);

        uint64_t cap = 3 * (seed_len > DIGEST ? seed_len : DIGEST);
        uint8_t *seed = malloc((size_t)cap), *a = malloc((size_t)cap), *b = malloc((size_t)cap),
                *cc = malloc((size_t)cap), *m = malloc((size_t)cap);
        uint64_t sl = seed_len, al, bl, cl;
        memcpy(seed, seed0, (size_t)seed_len);
        for (uint64_t j = 0; j < count; j++) {
            uint8_t md[DIGEST];
            memcpy(a, seed, (size_t)sl);
            memcpy(b, seed, (size_t)sl);
            memcpy(cc, seed, (size_t)sl);
            al = bl = cl = sl;
            for (int i = 0; i < 1000; i++) {
                uint64_t ml = al + bl + cl;
                memcpy(m, a, (size_t)al);
                memcpy(m + al, b, (size_t)bl);
                memcpy(m + al + bl, cc, (size_t)cl);
                if (variant == 2) {
                    if (ml >= seed_len) {
                        ml = seed_len;
                    } else {
                        memset(m + ml, 0, (size_t)(seed_len - ml));
                        ml = seed_len;
                    }
                } else if (variant != 1) {
                    fprintf(stderr, "%s: unknown Monte Carlo variant\n", c->name);
                    exit(2);
                }
                if (!hash_checked(m, ml, md)) bad++;
                memcpy(a, b, (size_t)bl);
                al = bl;
                memcpy(b, cc, (size_t)cl);
                bl = cl;
                memcpy(cc, md, DIGEST);
                cl = DIGEST;
            }
            if (memcmp(md, want + j * DIGEST, DIGEST) != 0) {
                if (bad < 5) fprintf(stderr, "%s: checkpoint %llu fails\n", c->name,
                                     (unsigned long long)j);
                bad++;
            }
            memcpy(seed, md, DIGEST);
            sl = DIGEST;
        }
        free(seed);
        free(a);
        free(b);
        free(cc);
        free(m);
    }
    return bad;
}

/*
 * Large message tests. The message is the content repeated to full length,
 * up to 8 GiB. It is not stored: one CHUNK of repeated content is mapped
 * again and again behind a private CHUNK that holds the byte list header,
 * so the byte part starts at offset CHUNK.
 */
#define CHUNK ((uint64_t)4 << 20)

#if defined(_WIN32)
static uint8_t *map_large(const uint8_t *content, uint64_t clen, uint64_t full) {
    HANDLE map = CreateFileMappingA(INVALID_HANDLE_VALUE, NULL, PAGE_READWRITE, 0, (DWORD)CHUNK, NULL);
    if (!map) return NULL;
    uint8_t *w = MapViewOfFile(map, FILE_MAP_WRITE, 0, 0, (SIZE_T)CHUNK);
    if (!w) return NULL;
    for (uint64_t i = 0; i < CHUNK; i += clen) memcpy(w + i, content, (size_t)clen);
    UnmapViewOfFile(w);
    uint64_t total = CHUNK + full, views = full / CHUNK;
    for (int attempt = 0; attempt < 16; attempt++) {
        uint8_t *base = VirtualAlloc(NULL, (SIZE_T)total, MEM_RESERVE, PAGE_NOACCESS);
        if (!base) return NULL;
        VirtualFree(base, 0, MEM_RELEASE);
        uint8_t *hdr = VirtualAlloc(base, (SIZE_T)CHUNK, MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE);
        uint64_t done = 0;
        if (hdr == base) {
            for (; done < views; done++) {
                void *want = base + CHUNK + done * CHUNK;
                if (MapViewOfFileEx(map, FILE_MAP_READ, 0, 0, (SIZE_T)CHUNK, want) != want) break;
            }
            if (done == views) return base;
        }
        for (uint64_t i = 0; i < done; i++) UnmapViewOfFile(base + CHUNK + i * CHUNK);
        if (hdr) VirtualFree(hdr, 0, MEM_RELEASE);
    }
    return NULL;
}
#else
static uint8_t *map_large(const uint8_t *content, uint64_t clen, uint64_t full) {
    char path[] = "/tmp/asm-crypto-ldt-XXXXXX";
    int fd = mkstemp(path);
    if (fd < 0) return NULL;
    unlink(path);
    if (ftruncate(fd, (off_t)CHUNK) != 0) return NULL;
    uint8_t *w = mmap(NULL, (size_t)CHUNK, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    if (w == MAP_FAILED) return NULL;
    for (uint64_t i = 0; i < CHUNK; i += clen) memcpy(w + i, content, (size_t)clen);
    munmap(w, (size_t)CHUNK);
    uint64_t total = CHUNK + full;
    uint8_t *base = mmap(NULL, (size_t)total, PROT_NONE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (base == MAP_FAILED) return NULL;
    if (mmap(base, (size_t)CHUNK, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON | MAP_FIXED, -1, 0) != base)
        return NULL;
    for (uint64_t off = CHUNK; off < total; off += CHUNK)
        if (mmap(base + off, (size_t)CHUNK, PROT_READ, MAP_SHARED | MAP_FIXED, fd, 0) != base + off)
            return NULL;
    close(fd);
    return base;
}
#endif

static int run_large(cursor *c, uint64_t n) {
    int bad = 0;
    for (uint64_t k = 0; k < n; k++) {
        uint64_t clen = take64(c);
        const uint8_t *content = take(c, clen);
        uint64_t full = take64(c);
        const uint8_t *want = take(c, DIGEST);
        if (clen == 0 || CHUNK % clen != 0 || full % CHUNK != 0) {
            fprintf(stderr, "%s: case %llu has a shape this runner cannot map\n", c->name,
                    (unsigned long long)k);
            exit(2);
        }
        uint8_t *base = map_large(content, clen, full);
        if (!base) {
            fprintf(stderr, "%s: case %llu: cannot map %llu bytes\n", c->name,
                    (unsigned long long)k, (unsigned long long)full);
            exit(2);
        }
        wr64(base + 0, CHUNK + full);
        wr64(base + 8, CHUNK);
        wr64(base + 16, full);
        uint64_t out[4];
        uint64_t status = sha256_checked(base, out);
        if (status != CRYPTO_OK || memcmp(out, want, DIGEST) != 0) {
            fprintf(stderr, "%s: case %llu (%llu bytes) fails\n", c->name, (unsigned long long)k,
                    (unsigned long long)full);
            bad++;
        }
        /* The mappings are left in place until the process ends. */
    }
    return bad;
}

static uint8_t *read_file(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *data = malloc(n > 0 ? (size_t)n : 1);
    if (!data || fread(data, 1, (size_t)n, f) != (size_t)n) {
        fclose(f);
        free(data);
        return NULL;
    }
    fclose(f);
    *len = (size_t)n;
    return data;
}

static int run_file(const char *dir, const char *name) {
    char path[4096];
    snprintf(path, sizeof path, "%s/%s", dir, name);
    size_t len = 0;
    uint8_t *data = read_file(path, &len);
    if (!data) {
        fprintf(stderr, "%s: cannot read\n", path);
        return 1;
    }
    cursor c = {data, data + len, name};
    if (memcmp(take(&c, 8), "SHA256V1", 8) != 0) {
        fprintf(stderr, "%s: wrong magic\n", name);
        exit(2);
    }
    uint64_t kind = take64(&c), n = take64(&c);
    int bad;
    if (kind == 1) bad = run_messages(&c, n);
    else if (kind == 2) bad = run_monte(&c, n);
    else if (kind == 3) bad = run_large(&c, n);
    else {
        fprintf(stderr, "%s: unknown kind\n", name);
        exit(2);
    }
    if (c.p != c.end) {
        fprintf(stderr, "%s: bytes left after the last case\n", name);
        exit(2);
    }
    printf("%s %s: %llu cases\n", bad ? "FAIL" : "PASS", name, (unsigned long long)n);
    free(data);
    return bad != 0;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: runner VECTOR_DIR [FILE ...]\n");
        return 2;
    }
    int failed = 0;
    if (argc == 2) {
        for (size_t i = 0; i < sizeof ALL_FILES / sizeof ALL_FILES[0]; i++)
            failed |= run_file(argv[1], ALL_FILES[i]);
    } else {
        for (int i = 2; i < argc; i++) failed |= run_file(argv[1], argv[i]);
    }
    int over = stack_peak > STACK_CAP;
    printf("%s stack crypto_sha256: %llu bytes, cap %d\n", over ? "FAIL" : "PASS", (unsigned long long)stack_peak,
           STACK_CAP);
    if (abi_fault)
        printf("FAIL abi crypto_sha256: kept state changed, mask 0x%016llx\n", (unsigned long long)abi_fault);
    else
        printf("PASS abi crypto_sha256: kept registers, stack pointer and flags\n");
    failed |= over || abi_fault;
    /* The verdict for the function, after every file ran. */
    if (argc == 2) printf("FUNCTION crypto_sha256 %s\n", failed ? "FAIL" : "PASS");
    return failed;
}
