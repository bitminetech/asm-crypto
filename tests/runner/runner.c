/*
 * Vector runner for asm-crypto.
 *
 * Usage: runner VECTOR_DIR [FILE ...]
 *
 * Reads the binary case files that tests/generator/ writes (formats in
 * tests/generator/README.md), calls the library for every case and compares
 * the results. With no FILE arguments it runs every file. It exits with
 * status 0 only when every case of every file it ran passes.
 *
 * Inputs sit at an offset with unused room after them, and must stay
 * unchanged. Fixed size outputs have guard bytes on both sides. ByteList
 * outputs and scratch buffers get exactly the size the function needs, with
 * guard bytes after them; one byte less must give CRYPTO_BUFFER_TOO_SMALL.
 *
 * Every call goes through abi_call (tests/runner/abi_<ISA>.s). The runner
 * prints the most stack each function used, and fails when a call uses more
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

/* C view of the interface in include/ and docs/reference/. */
#if defined(_WIN32) && defined(__x86_64__)
#define CRYPTO_ABI __attribute__((sysv_abi))
#else
#define CRYPTO_ABI
#endif
CRYPTO_ABI uint64_t crypto_sha256(const void *message, void *digest);
CRYPTO_ABI uint64_t crypto_keccak256(const void *message, void *digest);
CRYPTO_ABI uint64_t crypto_hmac_sha256(const void *key, const void *message, void *scratch, void *mac);
CRYPTO_ABI uint64_t crypto_hkdf_extract(const void *salt, const void *ikm, void *scratch, void *prk);
CRYPTO_ABI uint64_t crypto_hkdf_expand(const void *prk, const void *info, const void *length, void *scratch,
                                       void *okm);
CRYPTO_ABI uint64_t crypto_aes128_ctr(const void *key, const void *counter, const void *input, void *output);
CRYPTO_ABI uint64_t crypto_aes128_gcm_ae(const void *key, const void *iv, const void *plaintext, const void *aad,
                                         void *sealed);
CRYPTO_ABI uint64_t crypto_aes128_gcm_ad(const void *key, const void *iv, const void *sealed, const void *aad,
                                         void *plaintext);
CRYPTO_ABI uint64_t crypto_secp256k1_public_key(const void *private_key, void *public_key);
CRYPTO_ABI uint64_t crypto_secp256k1_decompress(const void *public_key, void *point);
CRYPTO_ABI uint64_t crypto_secp256k1_ecdh(const void *public_key, const void *private_key, void *shared);
CRYPTO_ABI uint64_t crypto_secp256k1_sign(const void *private_key, const void *hash, void *signature);
CRYPTO_ABI uint64_t crypto_secp256k1_verify(const void *public_key, const void *hash, const void *signature,
                                            void *valid);

/*
 * ABI and stack check. abi_call sets every register the callee must keep to a
 * known value and paints PAINT_BYTES of stack below the call. Afterwards it
 * reports the kept state that changed, and the bytes of stack the call used,
 * its return address included on x86-64. The layout of its record is in
 * tests/runner/README.md.
 */
#define STACK_CAP 4096 /* README: stack per call */
#define PAINT_BYTES (STACK_CAP + 4096)

typedef struct {
    uint64_t fn, arg[5], paint, status, fault, stack, scratch[4];
} abi_ctx;
CRYPTO_ABI void abi_call(abi_ctx *ctx);

enum { F_SHA256, F_KECCAK, F_HMAC, F_EXTRACT, F_EXPAND, F_CTR, F_GCM_AE, F_GCM_AD, F_PUBLIC_KEY, F_DECOMPRESS,
       F_ECDH, F_SIGN, F_VERIFY, F_COUNT };
static const char *const fn_name[F_COUNT] = {
    "crypto_sha256", "crypto_keccak256", "crypto_hmac_sha256", "crypto_hkdf_extract", "crypto_hkdf_expand",
    "crypto_aes128_ctr", "crypto_aes128_gcm_ae", "crypto_aes128_gcm_ad", "crypto_secp256k1_public_key",
    "crypto_secp256k1_decompress", "crypto_secp256k1_ecdh", "crypto_secp256k1_sign", "crypto_secp256k1_verify",
};
static uint64_t stack_peak[F_COUNT], abi_fault[F_COUNT], fn_cases[F_COUNT], fn_bad[F_COUNT];

/* Call function fn with its pointer arguments, through abi_call. */
static uint64_t checked_call(int fn, const void *const *args, size_t n) {
    static const void *const address[F_COUNT] = {
        (const void *)crypto_sha256, (const void *)crypto_keccak256, (const void *)crypto_hmac_sha256,
        (const void *)crypto_hkdf_extract, (const void *)crypto_hkdf_expand, (const void *)crypto_aes128_ctr,
        (const void *)crypto_aes128_gcm_ae, (const void *)crypto_aes128_gcm_ad,
        (const void *)crypto_secp256k1_public_key, (const void *)crypto_secp256k1_decompress,
        (const void *)crypto_secp256k1_ecdh, (const void *)crypto_secp256k1_sign,
        (const void *)crypto_secp256k1_verify,
    };
    abi_ctx c;
    memset(&c, 0, sizeof c);
    c.fn = (uint64_t)(uintptr_t)address[fn];
    for (size_t i = 0; i < n; i++) c.arg[i] = (uint64_t)(uintptr_t)args[i];
    c.paint = PAINT_BYTES;
    abi_call(&c);
    if (c.stack > stack_peak[fn]) stack_peak[fn] = c.stack;
    abi_fault[fn] |= c.fault;
    return c.status;
}

#define CALL(fn, ...)                                                                                          \
    checked_call(fn, (const void *const[]){__VA_ARGS__}, sizeof((const void *const[]){__VA_ARGS__}) / sizeof(void *))

/* crypto_sha256(message, digest), through abi_call. */
static uint64_t sha256_checked(const void *message, void *digest) { return CALL(F_SHA256, message, digest); }

#define CRYPTO_OK 0
#define BYTES_FIXED 24
#define DIGEST 32

static const char *ALL_FILES[] = {
    "cavp-short.bin", "cavp-long.bin", "boundary.bin", "acvp-aft.bin", "cavp-monte.bin", "acvp-mct.bin",
    "acvp-ldt.bin", "keccak-generated.bin", "hmac-wycheproof.bin", "hmac-generated.bin", "hkdf-wycheproof.bin",
    "hkdf-generated.bin", "aes-kat.bin", "aes-ctr-generated.bin", "gcm-cavp.bin", "gcm-wycheproof.bin",
    "gcm-generated.bin", "secp256k1-generated.bin", "ecdsa-wycheproof.bin", "ecdh-wycheproof.bin", "devp2p.bin",
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

/* ---------------------------------------------------------------- Keccak, HMAC, HKDF, AES and secp256k1 */

enum { HKDF_LENGTH = 2, GCM_FAIL = 3, INVALID_PRIVATE_KEY = 4, INVALID_PUBLIC_KEY = 5, BUFFER_TOO_SMALL = 1 };
enum { K_KECCAK = 1, K_HMAC, K_HKDF, K_CTR, K_GCM, K_PUBLIC_KEY, K_DECOMPRESS, K_ECDH, K_SIGN, K_VERIFY };

#define GUARD 16
#define FILL 0x5A

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) {
        fprintf(stderr, "out of memory\n");
        exit(2);
    }
    return p;
}

/* An input buffer, with a copy to check that the call left it unchanged. */
typedef struct {
    uint8_t *p, *copy;
    size_t n;
} input;

static input in_bytes(const uint8_t *b, size_t n) {
    input r = {xmalloc(n), xmalloc(n), n};
    memcpy(r.p, b, n);
    memcpy(r.copy, b, n);
    return r;
}

/* A ByteList input: the bytes at offset 32, then 7 bytes of unused room. */
static input in_list(const uint8_t *b, uint64_t len) {
    size_t size = (size_t)(32 + len + 7);
    input r = {xmalloc(size), xmalloc(size), size};
    memset(r.p, 0xA5, size);
    wr64(r.p, size);
    wr64(r.p + 8, 32);
    wr64(r.p + 16, len);
    if (len) memcpy(r.p + 32, b, (size_t)len);
    memcpy(r.copy, r.p, size);
    return r;
}

static int in_done(input *r) {
    int ok = memcmp(r->p, r->copy, r->n) == 0;
    free(r->p);
    free(r->copy);
    return ok;
}

/* An output or scratch buffer of n bytes, with GUARD bytes on both sides. */
typedef struct {
    uint8_t *base, *p;
    size_t n;
} output;

static output out_new(size_t n) {
    output r;
    r.base = xmalloc(n + 2 * GUARD);
    r.p = r.base + GUARD;
    r.n = n;
    memset(r.base, FILL, n + 2 * GUARD);
    return r;
}

/* A ByteList output or a scratch buffer: size field set, the rest filled. */
static output out_sized(size_t n) {
    output r = out_new(n);
    wr64(r.p, n);
    return r;
}

static int out_guards(output *r) {
    int ok = 1;
    for (int i = 0; i < GUARD; i++) ok &= r->base[i] == FILL && r->p[r->n + i] == FILL;
    return ok;
}

/* Guards intact and, for a ByteList, offset 24, count n and the bytes want. */
static int out_list_is(output *r, const uint8_t *want, uint64_t n) {
    return out_guards(r) && rd64(r->p) == r->n && rd64(r->p + 8) == 24 && rd64(r->p + 16) == n &&
           (n == 0 || memcmp(r->p + 24, want, (size_t)n) == 0);
}

static void out_free(output *r) { free(r->base); }

typedef struct {
    const uint8_t *p;
    uint64_t n;
} blob;

static blob take_blob(cursor *c) {
    blob b;
    b.n = take64(c);
    b.p = take(c, b.n);
    return b;
}

static int note(int fn, int ok, const char *file, const char *name) {
    fn_cases[fn]++;
    if (!ok) {
        if (fn_bad[fn] < 5) fprintf(stderr, "%s: %s: %s fails\n", file, name, fn_name[fn]);
        fn_bad[fn]++;
    }
    return ok;
}

static int case_keccak(cursor *c, const char *name) {
    blob msg = take_blob(c);
    const uint8_t *want = take(c, 32);
    input m = in_list(msg.p, msg.n);
    output d = out_new(32);
    uint64_t status = CALL(F_KECCAK, m.p, d.p);
    int ok = status == 0 && out_guards(&d) && memcmp(d.p, want, 32) == 0;
    ok &= in_done(&m);
    out_free(&d);
    return note(F_KECCAK, ok, c->name, name);
}

/* HMAC: exact scratch and one byte less. Scratch: 96 + message bytes. */
static int case_hmac(cursor *c, const char *name) {
    blob key = take_blob(c), msg = take_blob(c);
    const uint8_t *want = take(c, 32);
    int ok = 1;
    for (int small = 0; small < 2; small++) {
        input k = in_list(key.p, key.n), m = in_list(msg.p, msg.n);
        output s = out_sized((size_t)(96 + msg.n - small)), mac = out_new(32);
        uint64_t status = CALL(F_HMAC, k.p, m.p, s.p, mac.p);
        if (small)
            ok &= status == BUFFER_TOO_SMALL && out_guards(&s);
        else
            ok &= status == 0 && out_guards(&s) && out_guards(&mac) && memcmp(mac.p, want, 32) == 0;
        ok &= in_done(&k) & in_done(&m);
        out_free(&s);
        out_free(&mac);
    }
    return note(F_HMAC, ok, c->name, name);
}

/* HKDF: Extract with exact scratch, then Expand with exact scratch and output, and one byte less of each. */
static int case_hkdf(cursor *c, const char *name) {
    blob salt = take_blob(c), ikm = take_blob(c), info = take_blob(c);
    uint64_t length = take64(c), want_status = take64(c);
    const uint8_t *want_prk = take(c, 32);
    blob okm = take_blob(c);

    int ok = 1;
    for (int small = 0; small < 2; small++) {
        input sa = in_list(salt.p, salt.n), ik = in_list(ikm.p, ikm.n);
        output s = out_sized((size_t)(96 + ikm.n - small)), prk = out_new(32);
        uint64_t status = CALL(F_EXTRACT, sa.p, ik.p, s.p, prk.p);
        if (small)
            ok &= status == BUFFER_TOO_SMALL && out_guards(&s);
        else
            ok &= status == 0 && out_guards(&s) && out_guards(&prk) && memcmp(prk.p, want_prk, 32) == 0;
        ok &= in_done(&sa) & in_done(&ik);
        out_free(&s);
        out_free(&prk);
    }
    note(F_EXTRACT, ok, c->name, name);

    ok = 1;
    uint8_t len8[8];
    wr64(len8, length);
    size_t out_size = (size_t)(24 + (want_status == 0 ? length : 0));
    for (int small = 0; small < 3; small++) {
        if (small && want_status != 0) break;
        input p = in_list(want_prk, 32), in = in_list(info.p, info.n), l = in_bytes(len8, 8);
        output s = out_sized((size_t)(129 + info.n - (small == 1))), o = out_sized(out_size - (small == 2));
        uint64_t status = CALL(F_EXPAND, p.p, in.p, l.p, s.p, o.p);
        if (small)
            ok &= status == BUFFER_TOO_SMALL && out_guards(&s) && out_guards(&o);
        else if (want_status != 0)
            ok &= status == want_status && out_guards(&s) && out_guards(&o);
        else
            ok &= status == 0 && out_guards(&s) && okm.n == length && out_list_is(&o, okm.p, okm.n);
        ok &= in_done(&p) & in_done(&in) & in_done(&l);
        out_free(&s);
        out_free(&o);
    }
    return note(F_EXPAND, ok, c->name, name);
}

static int case_ctr(cursor *c, const char *name) {
    const uint8_t *key = take(c, 16), *counter = take(c, 16);
    blob in = take_blob(c), want = take_blob(c);
    int ok = want.n == in.n;
    for (int small = 0; small < 2; small++) {
        input k = in_bytes(key, 16), ct = in_bytes(counter, 16), i = in_list(in.p, in.n);
        output o = out_sized((size_t)(24 + in.n - small));
        uint64_t status = CALL(F_CTR, k.p, ct.p, i.p, o.p);
        if (small)
            ok &= status == BUFFER_TOO_SMALL && out_guards(&o);
        else
            ok &= status == 0 && out_list_is(&o, want.p, want.n);
        ok &= in_done(&k) & in_done(&ct) & in_done(&i);
        out_free(&o);
    }
    return note(F_CTR, ok, c->name, name);
}

static int case_gcm(cursor *c, const char *name) {
    const uint8_t *key = take(c, 16), *iv = take(c, 12);
    blob aad = take_blob(c), pt = take_blob(c), sealed = take_blob(c);
    uint64_t want_status = take64(c);
    int ok = 1;

    if (want_status == 0) {
        ok = sealed.n == pt.n + 16;
        for (int small = 0; small < 2; small++) {
            input k = in_bytes(key, 16), v = in_bytes(iv, 12), p = in_list(pt.p, pt.n), a = in_list(aad.p, aad.n);
            output o = out_sized((size_t)(24 + pt.n + 16 - small));
            uint64_t status = CALL(F_GCM_AE, k.p, v.p, p.p, a.p, o.p);
            if (small)
                ok &= status == BUFFER_TOO_SMALL && out_guards(&o);
            else
                ok &= status == 0 && out_list_is(&o, sealed.p, sealed.n);
            ok &= in_done(&k) & in_done(&v) & in_done(&p) & in_done(&a);
            out_free(&o);
        }
        note(F_GCM_AE, ok, c->name, name);
        ok = 1;
    }
    uint64_t pt_size = sealed.n >= 16 ? sealed.n - 16 : 0;
    for (int small = 0; small < 2; small++) {
        if (small && (want_status != 0)) break;
        input k = in_bytes(key, 16), v = in_bytes(iv, 12), s = in_list(sealed.p, sealed.n), a = in_list(aad.p, aad.n);
        output o = out_sized((size_t)(24 + pt_size - small));
        uint64_t status = CALL(F_GCM_AD, k.p, v.p, s.p, a.p, o.p);
        if (small)
            ok &= status == BUFFER_TOO_SMALL && out_guards(&o);
        else if (want_status != 0)
            ok &= status == want_status && out_guards(&o);
        else
            ok &= status == 0 && out_list_is(&o, pt.p, pt.n);
        ok &= in_done(&k) & in_done(&v) & in_done(&s) & in_done(&a);
        out_free(&o);
    }
    return note(F_GCM_AD, ok, c->name, name);
}

/* A function of one or two fixed inputs and one fixed output, against a status and bytes. */
static int case_fixed(int fn, const uint8_t *a, size_t an, const uint8_t *b, size_t bn, uint64_t want_status,
                      const uint8_t *want, size_t wn, const char *file, const char *name) {
    input x = in_bytes(a, an), y = in_bytes(b ? b : a, b ? bn : an);
    output o = out_new(wn);
    uint64_t status = b ? CALL(fn, x.p, y.p, o.p) : CALL(fn, x.p, o.p);
    int ok = status == want_status && out_guards(&o) && (want_status != 0 || memcmp(o.p, want, wn) == 0);
    ok &= in_done(&x) & in_done(&y);
    out_free(&o);
    return note(fn, ok, file, name);
}

static int case_verify(cursor *c, const char *name) {
    const uint8_t *pub = take(c, 33), *hash = take(c, 32), *sig = take(c, 64);
    uint64_t want_status = take64(c), want_valid = take64(c);
    input p = in_bytes(pub, 33), h = in_bytes(hash, 32), s = in_bytes(sig, 64);
    output v = out_new(8);
    uint64_t status = CALL(F_VERIFY, p.p, h.p, s.p, v.p);
    int ok = status == want_status && out_guards(&v) && (status != 0 || rd64(v.p) == want_valid);
    ok &= in_done(&p) & in_done(&h) & in_done(&s);
    out_free(&v);
    return note(F_VERIFY, ok, c->name, name);
}

/* One CRYPTOV2 file: each case is its kind, its name, then the fields of that kind. */
static int run_primitives(cursor *c, uint64_t n) {
    int bad = 0;
    for (uint64_t k = 0; k < n; k++) {
        uint64_t kind = take64(c);
        blob nm = take_blob(c);
        char name[256];
        snprintf(name, sizeof name, "%.*s", (int)(nm.n < 255 ? nm.n : 255), (const char *)nm.p);
        int ok;
        if (kind == K_KECCAK) ok = case_keccak(c, name);
        else if (kind == K_HMAC) ok = case_hmac(c, name);
        else if (kind == K_HKDF) ok = case_hkdf(c, name);
        else if (kind == K_CTR) ok = case_ctr(c, name);
        else if (kind == K_GCM) ok = case_gcm(c, name);
        else if (kind == K_PUBLIC_KEY) {
            const uint8_t *priv = take(c, 32);
            uint64_t st = take64(c);
            ok = case_fixed(F_PUBLIC_KEY, priv, 32, NULL, 0, st, take(c, 33), 33, c->name, name);
        } else if (kind == K_DECOMPRESS) {
            const uint8_t *pub = take(c, 33);
            uint64_t st = take64(c);
            ok = case_fixed(F_DECOMPRESS, pub, 33, NULL, 0, st, take(c, 64), 64, c->name, name);
        } else if (kind == K_ECDH) {
            const uint8_t *pub = take(c, 33), *priv = take(c, 32);
            uint64_t st = take64(c);
            ok = case_fixed(F_ECDH, pub, 33, priv, 32, st, take(c, 33), 33, c->name, name);
        } else if (kind == K_SIGN) {
            const uint8_t *priv = take(c, 32), *hash = take(c, 32);
            uint64_t st = take64(c);
            ok = case_fixed(F_SIGN, priv, 32, hash, 32, st, take(c, 64), 64, c->name, name);
        } else if (kind == K_VERIFY) ok = case_verify(c, name);
        else {
            fprintf(stderr, "%s: unknown kind %llu\n", c->name, (unsigned long long)kind);
            exit(2);
        }
        bad += !ok;
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
    const uint8_t *magic = take(&c, 8);
    int bad;
    uint64_t n;
    if (memcmp(magic, "CRYPTOV2", 8) == 0) {
        n = take64(&c);
        bad = run_primitives(&c, n);
    } else if (memcmp(magic, "SHA256V1", 8) == 0) {
        uint64_t kind = take64(&c);
        n = take64(&c);
        if (kind == 1) bad = run_messages(&c, n);
        else if (kind == 2) bad = run_monte(&c, n);
        else if (kind == 3) bad = run_large(&c, n);
        else {
            fprintf(stderr, "%s: unknown kind\n", name);
            exit(2);
        }
        fn_cases[F_SHA256] += n;
        fn_bad[F_SHA256] += (uint64_t)bad;
    } else {
        fprintf(stderr, "%s: wrong magic\n", name);
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
    for (int f = 0; f < F_COUNT; f++) {
        if (!fn_cases[f]) continue;
        int over = stack_peak[f] > STACK_CAP;
        printf("%s stack %s: %llu bytes, cap %d\n", over ? "FAIL" : "PASS", fn_name[f],
               (unsigned long long)stack_peak[f], STACK_CAP);
        if (abi_fault[f])
            printf("FAIL abi %s: kept state changed, mask 0x%016llx\n", fn_name[f], (unsigned long long)abi_fault[f]);
        else
            printf("PASS abi %s: kept registers, stack pointer and flags\n", fn_name[f]);
        int bad = over || abi_fault[f] || fn_bad[f];
        failed |= bad;
        /* The verdict for the function, after every file ran. */
        if (argc == 2) printf("FUNCTION %s %s\n", fn_name[f], bad ? "FAIL" : "PASS");
    }
    return failed;
}
