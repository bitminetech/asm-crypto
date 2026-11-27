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
 * than STACK_CAP, the stack limit, or changes state that the ABI says it must keep.
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

#ifdef CRYPTO_SHA_VARIANT
/* The CPU features of the sha variant (sha-256.md, The sha variant). */
#if defined(__x86_64__)
#include <cpuid.h>
static int sha_variant_supported(void) {
    unsigned a, b, c, d;
    if (!__get_cpuid(1, &a, &b, &c, &d) || !(c & bit_SSSE3)) return 0;
    if (!__get_cpuid_count(7, 0, &a, &b, &c, &d)) return 0;
    return (b & bit_SHA) != 0;
}
#elif defined(_WIN32)
static int sha_variant_supported(void) { return IsProcessorFeaturePresent(PF_ARM_V8_CRYPTO_INSTRUCTIONS_AVAILABLE) != 0; }
#elif defined(__APPLE__)
#include <sys/sysctl.h>
static int sha_variant_supported(void) {
    int v = 0;
    size_t n = sizeof v;
    return sysctlbyname("hw.optional.arm.FEAT_SHA256", &v, &n, NULL, 0) == 0 && v == 1;
}
#else
#include <sys/auxv.h>
static int sha_variant_supported(void) { return (getauxval(AT_HWCAP) & (1UL << 6)) != 0; }   /* HWCAP_SHA2 */
#endif
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
CRYPTO_ABI uint64_t crypto_chacha20_aead_encrypt(const void *key, const void *nonce, const void *plaintext,
                                                 const void *aad, void *sealed);
CRYPTO_ABI uint64_t crypto_chacha20_aead_decrypt(const void *key, const void *nonce, const void *sealed,
                                                 const void *aad, void *plaintext);
CRYPTO_ABI uint64_t crypto_poly1305_mac(const void *key, const void *message, void *tag);
CRYPTO_ABI uint64_t crypto_x25519(const void *scalar, const void *u, void *result);
CRYPTO_ABI uint64_t crypto_p256_public_key(const void *private_key, void *public_key);
CRYPTO_ABI uint64_t crypto_p256_ecdh(const void *public_key, const void *private_key, void *shared);
CRYPTO_ABI uint64_t crypto_p256_sign(const void *private_key, const void *hash, void *signature);
CRYPTO_ABI uint64_t crypto_p256_verify(const void *public_key, const void *hash, const void *signature, void *valid);
CRYPTO_ABI uint64_t crypto_sha512(const void *message, void *digest);
CRYPTO_ABI uint64_t crypto_sha512_init(void *state);
CRYPTO_ABI uint64_t crypto_sha512_update(void *state, const void *message);
CRYPTO_ABI uint64_t crypto_sha512_final(void *state, void *digest);
CRYPTO_ABI uint64_t crypto_ed25519_public_key(const void *private_key, void *public_key);
CRYPTO_ABI uint64_t crypto_ed25519_sign(const void *private_key, const void *message, void *signature);
CRYPTO_ABI uint64_t crypto_ed25519_verify(const void *public_key, const void *message, const void *signature,
                                          void *valid);
CRYPTO_ABI uint64_t crypto_bls_sk_to_pk(const void *secret_key, void *public_key);
CRYPTO_ABI uint64_t crypto_bls_sign(const void *secret_key, const void *message, void *scratch, void *signature);
CRYPTO_ABI uint64_t crypto_bls_verify(const void *public_key, const void *message, const void *signature, void *scratch,
                                      void *valid);
CRYPTO_ABI uint64_t crypto_bls_aggregate(const void *signatures, void *signature);
CRYPTO_ABI uint64_t crypto_bls_fast_aggregate_verify(const void *public_keys, const void *message, const void *signature,
                                                     void *scratch, void *valid);
CRYPTO_ABI uint64_t crypto_bls_key_validate(const void *public_key, void *valid);
CRYPTO_ABI uint64_t crypto_bls_eth_aggregate_pubkeys(const void *public_keys, void *public_key);
CRYPTO_ABI uint64_t crypto_bls_eth_fast_aggregate_verify(const void *public_keys, const void *message,
                                                         const void *signature, void *scratch, void *valid);
CRYPTO_ABI uint64_t crypto_bls_fast_aggregate_verify_cached(const void *keys, const void *indices, void *cache,
                                                            const void *message, const void *signature, void *scratch,
                                                            void *valid);
CRYPTO_ABI uint64_t crypto_bls_key_cache_fill(const void *keys, uint64_t first, uint64_t count, void *cache);
CRYPTO_ABI uint64_t crypto_bls_g1_decode(const void *bytes, void *point);
CRYPTO_ABI uint64_t crypto_bls_g1_compress(const void *point, void *bytes);
CRYPTO_ABI uint64_t crypto_bls_g1_add(const void *first, const void *second, void *point);
CRYPTO_ABI uint64_t crypto_bls_g1_neg(const void *point, void *negated);
CRYPTO_ABI uint64_t crypto_bls_g2_decode(const void *bytes, void *point);
CRYPTO_ABI uint64_t crypto_bls_g2_compress(const void *point, void *bytes);
CRYPTO_ABI uint64_t crypto_bls_expand_message_xmd(const void *message, const void *dst, const void *length,
                                                  void *scratch, void *uniform);
CRYPTO_ABI uint64_t crypto_bls_hash_to_g2(const void *message, const void *dst, void *scratch, void *point);
CRYPTO_ABI uint64_t crypto_kzg_trusted_setup_of_bytes(const void *g1_lagrange, const void *g1_monomial,
                                                      const void *g2_monomial, void *settings);
CRYPTO_ABI uint64_t crypto_kzg_blob_to_kzg_commitment(const void *settings, const void *blob, void *scratch,
                                                      void *commitment);
CRYPTO_ABI uint64_t crypto_kzg_compute_kzg_proof(const void *settings, const void *blob, const void *z, void *scratch,
                                                 void *proof, void *y);
CRYPTO_ABI uint64_t crypto_kzg_verify_kzg_proof(const void *settings, const void *commitment, const void *z,
                                                const void *y, const void *proof, void *scratch, void *valid);
CRYPTO_ABI uint64_t crypto_kzg_compute_blob_kzg_proof(const void *settings, const void *blob, const void *commitment,
                                                      void *scratch, void *proof);
CRYPTO_ABI uint64_t crypto_kzg_verify_blob_kzg_proof(const void *settings, const void *blob, const void *commitment,
                                                     const void *proof, void *scratch, void *valid);
CRYPTO_ABI uint64_t crypto_kzg_verify_blob_kzg_proof_batch(const void *settings, const void *blobs,
                                                           const void *commitments, const void *proofs, void *scratch,
                                                           void *valid);
CRYPTO_ABI uint64_t crypto_kzg_compute_challenge(const void *blob, const void *commitment, void *scratch,
                                                 void *challenge);
CRYPTO_ABI uint64_t crypto_kzg_compute_cells(const void *blob, void *scratch, void *cells);
CRYPTO_ABI uint64_t crypto_kzg_compute_cells_and_kzg_proofs(const void *settings, const void *blob, void *scratch,
                                                            void *cells, void *proofs);
CRYPTO_ABI uint64_t crypto_kzg_verify_cell_kzg_proof_batch(const void *settings, const void *commitments,
                                                           const void *cell_indices, const void *cells,
                                                           const void *proofs, void *scratch, void *valid);
CRYPTO_ABI uint64_t crypto_kzg_recover_cells_and_kzg_proofs(const void *settings, const void *cell_indices,
                                                            const void *cells, void *scratch, void *recovered_cells,
                                                            void *recovered_proofs);
CRYPTO_ABI uint64_t crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge(const void *commitments,
                                                                             const void *commitment_indices,
                                                                             const void *cell_indices, const void *cells,
                                                                             const void *proofs, void *scratch,
                                                                             void *challenge);

/*
 * ABI and stack check. abi_call sets every register the callee must keep to a
 * known value and paints PAINT_BYTES of stack below the call. Afterwards it
 * reports the kept state that changed, and the bytes of stack the call used,
 * its return address included on x86-64. The layout of its record is in
 * tests/runner/README.md.
 */
#define STACK_CAP 4096 /* the stack limit (ARCHITECTURE.md section 6) */
#define PAINT_BYTES (STACK_CAP + 4096)

typedef struct {
    uint64_t fn, arg[5], paint, status, fault, stack, scratch[4], more[2];
} abi_ctx;
CRYPTO_ABI void abi_call(abi_ctx *ctx);

enum { F_SHA256, F_KECCAK, F_HMAC, F_EXTRACT, F_EXPAND, F_CTR, F_GCM_AE, F_GCM_AD, F_PUBLIC_KEY, F_DECOMPRESS,
       F_ECDH, F_SIGN, F_VERIFY, F_CHACHA_ENC, F_CHACHA_DEC, F_POLY1305_MAC, F_X25519, F_P256_PUBLIC_KEY, F_P256_ECDH,
       F_P256_SIGN, F_P256_VERIFY, F_SHA512, F_SHA512_INIT, F_SHA512_UPDATE, F_SHA512_FINAL, F_ED25519_PUBLIC_KEY,
       F_ED25519_SIGN, F_ED25519_VERIFY, F_BLS_SK_TO_PK, F_BLS_SIGN, F_BLS_VERIFY, F_BLS_AGGREGATE, F_BLS_FAST,
       F_BLS_KEY_VALIDATE, F_BLS_ETH_AGGREGATE, F_BLS_ETH_FAST, F_BLS_G1_DECODE, F_BLS_G1_COMPRESS, F_BLS_G1_ADD,
       F_BLS_G1_NEG, F_BLS_G2_DECODE, F_BLS_G2_COMPRESS, F_BLS_XMD, F_BLS_HASH_TO_G2, F_KZG_SETUP, F_KZG_COMMIT,
       F_KZG_PROOF, F_KZG_VERIFY, F_KZG_BLOB_PROOF, F_KZG_BLOB_VERIFY, F_KZG_BLOB_BATCH, F_KZG_CHALLENGE, F_KZG_CELLS,
       F_KZG_CELLS_PROOFS, F_KZG_CELL_BATCH, F_KZG_RECOVER, F_KZG_CELL_CHALLENGE, F_BLS_FAST_CACHED, F_BLS_CACHE_FILL, F_COUNT };
static const char *const fn_name[F_COUNT] = {
    "crypto_sha256", "crypto_keccak256", "crypto_hmac_sha256", "crypto_hkdf_extract", "crypto_hkdf_expand",
    "crypto_aes128_ctr", "crypto_aes128_gcm_ae", "crypto_aes128_gcm_ad", "crypto_secp256k1_public_key",
    "crypto_secp256k1_decompress", "crypto_secp256k1_ecdh", "crypto_secp256k1_sign", "crypto_secp256k1_verify",
    "crypto_chacha20_aead_encrypt", "crypto_chacha20_aead_decrypt", "crypto_poly1305_mac", "crypto_x25519",
    "crypto_p256_public_key", "crypto_p256_ecdh",
    "crypto_p256_sign", "crypto_p256_verify", "crypto_sha512", "crypto_sha512_init", "crypto_sha512_update",
    "crypto_sha512_final", "crypto_ed25519_public_key", "crypto_ed25519_sign", "crypto_ed25519_verify",
    "crypto_bls_sk_to_pk", "crypto_bls_sign", "crypto_bls_verify", "crypto_bls_aggregate",
    "crypto_bls_fast_aggregate_verify", "crypto_bls_key_validate", "crypto_bls_eth_aggregate_pubkeys",
    "crypto_bls_eth_fast_aggregate_verify", "crypto_bls_g1_decode", "crypto_bls_g1_compress", "crypto_bls_g1_add",
    "crypto_bls_g1_neg", "crypto_bls_g2_decode", "crypto_bls_g2_compress", "crypto_bls_expand_message_xmd",
    "crypto_bls_hash_to_g2", "crypto_kzg_trusted_setup_of_bytes", "crypto_kzg_blob_to_kzg_commitment",
    "crypto_kzg_compute_kzg_proof", "crypto_kzg_verify_kzg_proof", "crypto_kzg_compute_blob_kzg_proof",
    "crypto_kzg_verify_blob_kzg_proof", "crypto_kzg_verify_blob_kzg_proof_batch", "crypto_kzg_compute_challenge",
    "crypto_kzg_compute_cells", "crypto_kzg_compute_cells_and_kzg_proofs", "crypto_kzg_verify_cell_kzg_proof_batch",
    "crypto_kzg_recover_cells_and_kzg_proofs", "crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge",
    "crypto_bls_fast_aggregate_verify_cached", "crypto_bls_key_cache_fill",
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
        (const void *)crypto_secp256k1_verify, (const void *)crypto_chacha20_aead_encrypt,
        (const void *)crypto_chacha20_aead_decrypt, (const void *)crypto_poly1305_mac, (const void *)crypto_x25519,
        (const void *)crypto_p256_public_key, (const void *)crypto_p256_ecdh,
        (const void *)crypto_p256_sign, (const void *)crypto_p256_verify, (const void *)crypto_sha512,
        (const void *)crypto_sha512_init, (const void *)crypto_sha512_update, (const void *)crypto_sha512_final,
        (const void *)crypto_ed25519_public_key, (const void *)crypto_ed25519_sign, (const void *)crypto_ed25519_verify,
        (const void *)crypto_bls_sk_to_pk, (const void *)crypto_bls_sign, (const void *)crypto_bls_verify,
        (const void *)crypto_bls_aggregate, (const void *)crypto_bls_fast_aggregate_verify,
        (const void *)crypto_bls_key_validate, (const void *)crypto_bls_eth_aggregate_pubkeys,
        (const void *)crypto_bls_eth_fast_aggregate_verify, (const void *)crypto_bls_g1_decode,
        (const void *)crypto_bls_g1_compress, (const void *)crypto_bls_g1_add, (const void *)crypto_bls_g1_neg,
        (const void *)crypto_bls_g2_decode, (const void *)crypto_bls_g2_compress,
        (const void *)crypto_bls_expand_message_xmd, (const void *)crypto_bls_hash_to_g2,
        (const void *)crypto_kzg_trusted_setup_of_bytes, (const void *)crypto_kzg_blob_to_kzg_commitment,
        (const void *)crypto_kzg_compute_kzg_proof, (const void *)crypto_kzg_verify_kzg_proof,
        (const void *)crypto_kzg_compute_blob_kzg_proof, (const void *)crypto_kzg_verify_blob_kzg_proof,
        (const void *)crypto_kzg_verify_blob_kzg_proof_batch, (const void *)crypto_kzg_compute_challenge,
        (const void *)crypto_kzg_compute_cells, (const void *)crypto_kzg_compute_cells_and_kzg_proofs,
        (const void *)crypto_kzg_verify_cell_kzg_proof_batch, (const void *)crypto_kzg_recover_cells_and_kzg_proofs,
        (const void *)crypto_kzg_compute_verify_cell_kzg_proof_batch_challenge,
        (const void *)crypto_bls_fast_aggregate_verify_cached, (const void *)crypto_bls_key_cache_fill,
    };
    abi_ctx c;
    memset(&c, 0, sizeof c);
    c.fn = (uint64_t)(uintptr_t)address[fn];
    for (size_t i = 0; i < n; i++) {
        if (i < 5)
            c.arg[i] = (uint64_t)(uintptr_t)args[i];
        else
            c.more[i - 5] = (uint64_t)(uintptr_t)args[i];
    }
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
    "chacha20-poly1305-rfc.bin", "chacha20-poly1305-wycheproof.bin", "chacha20-poly1305-generated.bin",
    "poly1305-rfc.bin", "poly1305-generated.bin",
    "x25519-rfc.bin", "x25519-wycheproof.bin", "x25519-generated.bin", "p256-rfc6979.bin", "p256-cavp.bin",
    "p256-wycheproof.bin", "p256-generated.bin", "sha512-cavp.bin", "sha512-generated.bin", "ed25519-rfc8032.bin",
    "ed25519-wycheproof.bin", "ed25519-generated.bin", "p256-rfc5903.bin", "p256-ecdh-cavp.bin",
    "p256-ecdh-wycheproof.bin", "p256-ecdh-generated.bin", "bls-official.bin", "bls-generated.bin",
    "kzg-generated.bin", "kzg-official.bin",
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

enum { HKDF_LENGTH = 2, GCM_FAIL = 3, INVALID_PRIVATE_KEY = 4, INVALID_PUBLIC_KEY = 5, CHACHA_FAIL = 6, X25519_ZERO = 7,
       BUFFER_TOO_SMALL = 1 };
enum { K_KECCAK = 1, K_HMAC, K_HKDF, K_CTR, K_GCM, K_PUBLIC_KEY, K_DECOMPRESS, K_ECDH, K_SIGN, K_VERIFY, K_CHACHA, K_X25519,
       K_P256_PUBLIC_KEY, K_P256_SIGN, K_P256_VERIFY, K_POLY1305, K_SHA512, K_ED25519_PUBLIC_KEY, K_ED25519_SIGN,
       K_ED25519_VERIFY, K_P256_ECDH, K_BLS_SK_TO_PK, K_BLS_SIGN, K_BLS_VERIFY, K_BLS_AGGREGATE, K_BLS_FAST,
       K_BLS_KEY_VALIDATE, K_BLS_ETH_AGGREGATE, K_BLS_ETH_FAST, K_BLS_G1_DECODE, K_BLS_G2_DECODE, K_BLS_G1_ADD,
       K_BLS_G1_NEG, K_BLS_XMD, K_BLS_HASH_TO_G2, K_KZG_SETUP, K_KZG_COMMIT, K_KZG_PROOF, K_KZG_VERIFY,
       K_KZG_BLOB_PROOF, K_KZG_BLOB_VERIFY, K_KZG_BLOB_BATCH, K_KZG_CHALLENGE, K_KZG_CELLS, K_KZG_CELLS_PROOFS,
       K_KZG_CELL_BATCH, K_KZG_RECOVER, K_KZG_CELL_CHALLENGE };

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

/* An AEAD case: GCM (key of 16 bytes) or ChaCha20-Poly1305 (key of 32 bytes), with a 12-byte IV and a 16-byte tag. */
static int case_aead(cursor *c, const char *name, int fn_ae, int fn_ad, size_t key_len) {
    const uint8_t *key = take(c, key_len), *iv = take(c, 12);
    blob aad = take_blob(c), pt = take_blob(c), sealed = take_blob(c);
    uint64_t want_status = take64(c);
    int ok = 1;

    if (want_status == 0) {
        ok = sealed.n == pt.n + 16;
        for (int small = 0; small < 2; small++) {
            input k = in_bytes(key, key_len), v = in_bytes(iv, 12), p = in_list(pt.p, pt.n), a = in_list(aad.p, aad.n);
            output o = out_sized((size_t)(24 + pt.n + 16 - small));
            uint64_t status = CALL(fn_ae, k.p, v.p, p.p, a.p, o.p);
            if (small)
                ok &= status == BUFFER_TOO_SMALL && out_guards(&o);
            else
                ok &= status == 0 && out_list_is(&o, sealed.p, sealed.n);
            ok &= in_done(&k) & in_done(&v) & in_done(&p) & in_done(&a);
            out_free(&o);
        }
        note(fn_ae, ok, c->name, name);
        ok = 1;
    }
    uint64_t pt_size = sealed.n >= 16 ? sealed.n - 16 : 0;
    for (int small = 0; small < 2; small++) {
        if (small && (want_status != 0)) break;
        input k = in_bytes(key, key_len), v = in_bytes(iv, 12), s = in_list(sealed.p, sealed.n), a = in_list(aad.p, aad.n);
        output o = out_sized((size_t)(24 + pt_size - small));
        uint64_t status = CALL(fn_ad, k.p, v.p, s.p, a.p, o.p);
        if (small)
            ok &= status == BUFFER_TOO_SMALL && out_guards(&o);
        else if (want_status != 0)
            ok &= status == want_status && out_guards(&o);
        else
            ok &= status == 0 && out_list_is(&o, pt.p, pt.n);
        ok &= in_done(&k) & in_done(&v) & in_done(&s) & in_done(&a);
        out_free(&o);
    }
    return note(fn_ad, ok, c->name, name);
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

/* An ECDSA check: a public key of pub_len bytes, a 32-byte hash, a 64-byte signature. */
static int case_verify(cursor *c, const char *name, int fn, size_t pub_len) {
    const uint8_t *pub = take(c, pub_len), *hash = take(c, 32), *sig = take(c, 64);
    uint64_t want_status = take64(c), want_valid = take64(c);
    input p = in_bytes(pub, pub_len), h = in_bytes(hash, 32), s = in_bytes(sig, 64);
    output v = out_new(8);
    uint64_t status = CALL(fn, p.p, h.p, s.p, v.p);
    int ok = status == want_status && out_guards(&v) && (status != 0 || rd64(v.p) == want_valid);
    ok &= in_done(&p) & in_done(&h) & in_done(&s);
    out_free(&v);
    return note(fn, ok, c->name, name);
}

/*
 * SHA-512: crypto_sha512 on the whole message, then the same message in three
 * parts through crypto_sha512_init, crypto_sha512_update and crypto_sha512_final.
 */
static int case_sha512(cursor *c, const char *name) {
    blob msg = take_blob(c);
    const uint8_t *want = take(c, 64);
    input m = in_list(msg.p, msg.n);
    output d = out_new(64);
    uint64_t status = CALL(F_SHA512, m.p, d.p);
    int ok = status == 0 && out_guards(&d) && memcmp(d.p, want, 64) == 0;
    ok &= in_done(&m);
    out_free(&d);
    note(F_SHA512, ok, c->name, name);

    uint64_t cut[4] = {0, msg.n / 3, msg.n - msg.n / 5, msg.n};
    output st = out_new(200), d2 = out_new(64);
    int parts = CALL(F_SHA512_INIT, st.p) == 0;
    for (int i = 0; i < 3; i++) {
        input part = in_list(msg.p + cut[i], cut[i + 1] - cut[i]);
        parts &= CALL(F_SHA512_UPDATE, st.p, part.p) == 0;
        parts &= in_done(&part);
    }
    parts &= CALL(F_SHA512_FINAL, st.p, d2.p) == 0;
    parts &= out_guards(&st) && out_guards(&d2) && memcmp(d2.p, want, 64) == 0;
    out_free(&st);
    out_free(&d2);
    note(F_SHA512_INIT, parts, c->name, name);
    note(F_SHA512_UPDATE, parts, c->name, name);
    note(F_SHA512_FINAL, parts, c->name, name);
    return ok && parts;
}

/* Ed25519 sign: a 32-byte private key and a message, against a 64-byte signature. */
static int case_ed25519_sign(cursor *c, const char *name) {
    const uint8_t *priv = take(c, 32);
    blob msg = take_blob(c);
    const uint8_t *want = take(c, 64);
    input k = in_bytes(priv, 32), m = in_list(msg.p, msg.n);
    output sig = out_new(64);
    uint64_t status = CALL(F_ED25519_SIGN, k.p, m.p, sig.p);
    int ok = status == 0 && out_guards(&sig) && memcmp(sig.p, want, 64) == 0;
    ok &= in_done(&k) & in_done(&m);
    out_free(&sig);
    return note(F_ED25519_SIGN, ok, c->name, name);
}

/* Ed25519 verify: a 32-byte public key, a message, a 64-byte signature, against a status and valid. */
static int case_ed25519_verify(cursor *c, const char *name) {
    const uint8_t *pub = take(c, 32);
    blob msg = take_blob(c);
    const uint8_t *sig = take(c, 64);
    uint64_t want_status = take64(c), want_valid = take64(c);
    input p = in_bytes(pub, 32), m = in_list(msg.p, msg.n), s = in_bytes(sig, 64);
    output v = out_new(8);
    uint64_t status = CALL(F_ED25519_VERIFY, p.p, m.p, s.p, v.p);
    int ok = status == want_status && out_guards(&v) && (status != 0 || rd64(v.p) == want_valid);
    ok &= in_done(&p) & in_done(&m) & in_done(&s);
    out_free(&v);
    return note(F_ED25519_VERIFY, ok, c->name, name);
}

/* One CRYPTOV2 file: each case is its kind, its name, then the fields of that kind. */

/* ---------------------------------------------------------------- BLS12-381 */

enum { INVALID_SIGNATURE = 8, EMPTY_LIST = 9, INVALID_ENCODING = 10, XMD_LENGTH = 11, POINT_AT_INFINITY = 12 };
#define BLS_SCRATCH 8192 /* include/bls12381.inc: CRYPTO_BLS_SCRATCH */
#define H2C_SCRATCH 4096 /* include/bls12381.inc: CRYPTO_BLS_H2C_SCRATCH */
#define G1_POINT 144
#define G2_POINT 288

/* A list of keys or signatures: entries of entry bytes at offset 32, then 7 bytes of unused room. */
static input in_entries(blob b, size_t entry) {
    input r = in_list(b.p, b.n);
    wr64(r.p + 16, b.n / entry);
    memcpy(r.copy, r.p, r.n);
    return r;
}

/* sign: the secret key is checked before scratch, so a bad key gives its status with any scratch. */
static int case_bls_sign(cursor *c, const char *name) {
    const uint8_t *sk = take(c, 32);
    blob msg = take_blob(c);
    uint64_t want_status = take64(c);
    const uint8_t *want = take(c, 96);
    int ok = 1;
    for (int small = 0; small < 2; small++) {
        input k = in_bytes(sk, 32), m = in_list(msg.p, msg.n);
        output s = out_sized((size_t)(BLS_SCRATCH + msg.n - small)), o = out_new(96);
        uint64_t status = CALL(F_BLS_SIGN, k.p, m.p, s.p, o.p);
        if (want_status != 0)
            ok &= status == want_status && out_guards(&s) && out_guards(&o);
        else if (small)
            ok &= status == BUFFER_TOO_SMALL && out_guards(&s) && out_guards(&o);
        else
            ok &= status == 0 && out_guards(&s) && out_guards(&o) && memcmp(o.p, want, 96) == 0;
        ok &= in_done(&k) & in_done(&m);
        out_free(&s);
        out_free(&o);
    }
    return note(F_BLS_SIGN, ok, c->name, name);
}

/* A check with scratch: verify, fast_aggregate_verify or eth_fast_aggregate_verify. keys is NULL for verify. */
static int case_bls_check(int fn, const blob *keys, const uint8_t *pk, blob msg, const uint8_t *sig, uint64_t want,
                          const char *file, const char *name) {
    int ok = 1;
    for (int small = 0; small < 2; small++) {
        input k = keys ? in_entries(*keys, 48) : in_bytes(pk, 48), m = in_list(msg.p, msg.n), g = in_bytes(sig, 96);
        output s = out_sized((size_t)(BLS_SCRATCH + msg.n - small)), v = out_new(8);
        uint64_t status = CALL(fn, k.p, m.p, g.p, s.p, v.p);
        if (small)
            ok &= status == BUFFER_TOO_SMALL && out_guards(&s) && out_guards(&v);
        else
            ok &= status == 0 && out_guards(&s) && out_guards(&v) && rd64(v.p) == want;
        ok &= in_done(&k) & in_done(&m) & in_done(&g);
        out_free(&s);
        out_free(&v);
    }
    return note(fn, ok, file, name);
}

/*
 * crypto_bls_fast_aggregate_verify_cached on the keys of a verify or fast aggregate case, n >= 1
 * of them, 48 bytes each (ARCHITECTURE.md section 5: every vector of the functions it stands
 * for). The runs, each with the case's expected result unless named:
 * - the keys at a stride of 48, the indices 0 to n - 1, a new cache: once, then again with the
 *   cache it filled, then with one scratch byte short (BUFFER_TOO_SMALL, the cache unchanged);
 * - the same with the cache that every case before filled (count CACHED_COUNT);
 * - each distinct key once at a stride of 128, in reverse order, with the index of each key
 *   (a repeated key gives a repeated index), a new cache;
 * - the indices 0 to n - 1 and then n, with a cache of count n: 0.
 * Each run checks the inputs unchanged, the guards of the cache, scratch and valid, the fixed
 * fields of the cache, and the entries past the ones read left at 0.
 */
#define CACHED_COUNT 256
#define CACHE_ENTRY 152 /* include/bls12381.inc: CRYPTO_BLS_ENTRY_BYTES */
static output new_key_cache(uint64_t stride, uint64_t count) {
    output r = out_new((size_t)(32 + CACHE_ENTRY * count));
    memset(r.p, 0, r.n);
    wr64(r.p, r.n);
    wr64(r.p + 8, stride);
    wr64(r.p + 16, 32);
    wr64(r.p + 24, count);
    return r;
}

static int cached_run(const uint8_t *keys, size_t keys_n, const uint64_t *idx, uint64_t n, output *cache, blob msg,
                      const uint8_t *sig, uint64_t want, int small, uint64_t untouched_from) {
    uint8_t *ib = xmalloc((size_t)(8 * n + 1));
    for (uint64_t k = 0; k < n; k++) wr64(ib + 8 * k, idx[k]);
    input k = in_bytes(keys, keys_n), l = in_list(ib, 8 * n), m = in_list(msg.p, msg.n), g = in_bytes(sig, 96);
    wr64(l.p + 16, n);
    memcpy(l.copy, l.p, l.n);
    uint8_t head[32], *before = xmalloc(cache->n);
    memcpy(head, cache->p, 32);
    memcpy(before, cache->p, cache->n);
    output s = out_sized((size_t)(BLS_SCRATCH + msg.n - (small ? 1 : 0))), v = out_new(8);
    uint64_t status = CALL(F_BLS_FAST_CACHED, k.p, l.p, cache->p, m.p, g.p, s.p, v.p);
    int ok = out_guards(cache) && out_guards(&s) && out_guards(&v) && memcmp(head, cache->p, 32) == 0;
    if (small) ok &= status == BUFFER_TOO_SMALL && memcmp(before, cache->p, cache->n) == 0;
    else ok &= status == 0 && rd64(v.p) == want;
    for (uint64_t e = untouched_from; e < rd64(cache->p + 24); e++)
        for (int b = 0; b < CACHE_ENTRY; b++) ok &= cache->p[32 + CACHE_ENTRY * e + b] == 0;
    ok &= in_done(&k) & in_done(&l) & in_done(&m) & in_done(&g);
    out_free(&s);
    out_free(&v);
    free(before);
    free(ib);
    return ok;
}

/*
 * crypto_bls_key_cache_fill (ARCHITECTURE.md section 5: the vectors of the functions it stands for):
 * entries 0 to n - 1 of a new cache of count n, filled in two calls that split the range at n / 2,
 * the second asking past the count, and a third call with no indices. Each entry: status 1 when
 * crypto_bls_key_validate gives 1 for its key, else 2, and its key; then
 * crypto_bls_fast_aggregate_verify_cached on that cache gives the case's result and changes no
 * entry of a key that passes. A fill of the cache again changes no byte; one of an entry holding
 * another key writes this key.
 */
static int fill_run(const uint8_t *keys, uint64_t n, blob msg, const uint8_t *sig, uint64_t want) {
    output cache = new_key_cache(48, n);
    input k = in_bytes(keys, (size_t)(48 * n));
    uint64_t half = n / 2;
    uint8_t head[32];
    memcpy(head, cache.p, 32);
    int ok = CALL(F_BLS_CACHE_FILL, k.p, (const void *)(uintptr_t)0, (const void *)(uintptr_t)half, cache.p) == 0;
    ok &= CALL(F_BLS_CACHE_FILL, k.p, (const void *)(uintptr_t)half, (const void *)(uintptr_t)(n - half + 7), cache.p) == 0;
    ok &= CALL(F_BLS_CACHE_FILL, k.p, (const void *)(uintptr_t)n, (const void *)(uintptr_t)UINT64_MAX, cache.p) == 0;
    ok &= out_guards(&cache) && memcmp(head, cache.p, 32) == 0;
    for (uint64_t e = 0; e < n && ok; e++) {
        const uint8_t *en = cache.p + 32 + CACHE_ENTRY * e;
        uint8_t v[8];
        crypto_bls_key_validate(keys + 48 * e, v);
        ok &= rd64(en) == (rd64(v) ? 1u : 2u) && memcmp(en + 8, keys + 48 * e, 48) == 0;
    }
    uint8_t *before = xmalloc(cache.n);
    memcpy(before, cache.p, cache.n);
    ok &= CALL(F_BLS_CACHE_FILL, k.p, (const void *)(uintptr_t)0, (const void *)(uintptr_t)n, cache.p) == 0 &&
          memcmp(before, cache.p, cache.n) == 0;
    if (ok && n > 1) { /* entry 0 holding key 1: the fill writes key 0 back */
        memcpy(cache.p + 32 + 8, keys + 48, 48);
        ok &= CALL(F_BLS_CACHE_FILL, k.p, (const void *)(uintptr_t)0, (const void *)(uintptr_t)1, cache.p) == 0 &&
              memcmp(before, cache.p, cache.n) == 0;
    }
    ok &= in_done(&k);
    uint64_t *idx = xmalloc((size_t)(8 * n));
    for (uint64_t e = 0; e < n; e++) idx[e] = e;
    ok &= cached_run(keys, (size_t)(48 * n), idx, n, &cache, msg, sig, want, 0, n);
    for (uint64_t e = 0; e < n && ok; e++)
        if (rd64(before + 32 + CACHE_ENTRY * e) == 1) ok &= memcmp(before + 32 + CACHE_ENTRY * e, cache.p + 32 + CACHE_ENTRY * e, CACHE_ENTRY) == 0;
    free(idx);
    free(before);
    out_free(&cache);
    return ok;
}

static int case_bls_cached(blob keys, blob msg, const uint8_t *sig, uint64_t want, const char *file,
                           const char *name) {
    static output shared;
    static int shared_made;
    uint64_t n = keys.n / 48, *idx = xmalloc((size_t)(8 * (n + 1)));
    if (n == 0 || n > CACHED_COUNT) {
        free(idx);
        return 1;
    }
    if (!shared_made) shared = new_key_cache(48, CACHED_COUNT), shared_made = 1;
    for (uint64_t k = 0; k <= n; k++) idx[k] = k;
    int ok = 1;
    output fresh = new_key_cache(48, CACHED_COUNT);
    ok &= cached_run(keys.p, (size_t)keys.n, idx, n, &fresh, msg, sig, want, 0, n);
    ok &= cached_run(keys.p, (size_t)keys.n, idx, n, &fresh, msg, sig, want, 0, n);
    ok &= cached_run(keys.p, (size_t)keys.n, idx, n, &fresh, msg, sig, want, 1, n);
    out_free(&fresh);
    ok &= cached_run(keys.p, (size_t)keys.n, idx, n, &shared, msg, sig, want, 0, CACHED_COUNT);
    /* Each distinct key once at a stride of 128, in reverse order. */
    uint64_t distinct = 0, *slot = xmalloc((size_t)(8 * n));
    uint8_t *wide = xmalloc((size_t)(128 * n));
    memset(wide, 0x5A, (size_t)(128 * n));
    for (uint64_t k = 0; k < n; k++) {
        uint64_t d = 0;
        while (d < k && memcmp(keys.p + 48 * d, keys.p + 48 * k, 48)) d++;
        slot[k] = d < k ? slot[d] : distinct++;
    }
    for (uint64_t k = 0; k < n; k++) {
        idx[k] = distinct - 1 - slot[k];
        memcpy(wide + 128 * idx[k], keys.p + 48 * k, 48);
    }
    output strided = new_key_cache(128, distinct);
    ok &= cached_run(wide, (size_t)(128 * distinct), idx, n, &strided, msg, sig, want, 0, distinct);
    out_free(&strided);
    /* An index at the count: 0. */
    for (uint64_t k = 0; k <= n; k++) idx[k] = k;
    output exact = new_key_cache(48, n);
    ok &= cached_run(keys.p, (size_t)keys.n, idx, n + 1, &exact, msg, sig, 0, 0, n);
    out_free(&exact);
    free(slot);
    free(wide);
    free(idx);
    ok = note(F_BLS_FAST_CACHED, ok, file, name);
    return note(F_BLS_CACHE_FILL, fill_run(keys.p, n, msg, sig, want), file, name) & ok;
}

/* A list function: aggregate (96-byte entries) or eth_aggregate_pubkeys (48-byte entries). */
static int case_bls_list(int fn, blob entries, size_t entry, uint64_t want_status, const uint8_t *want, size_t wn,
                         const char *file, const char *name) {
    input l = in_entries(entries, entry);
    output o = out_new(wn);
    uint64_t status = CALL(fn, l.p, o.p);
    int ok = status == want_status && out_guards(&o) && (want_status != 0 || memcmp(o.p, want, wn) == 0);
    ok &= in_done(&l);
    out_free(&o);
    return note(fn, ok, file, name);
}

/* Decode and compress again: G1 (48 bytes, point 144) or G2 (96 bytes, point 288). */
static int case_bls_decode(int dec, int comp, const uint8_t *b, size_t bn, size_t pn, uint64_t want_status,
                           const uint8_t *want, const char *file, const char *name) {
    input i = in_bytes(b, bn);
    output pt = out_new(pn);
    uint64_t status = CALL(dec, i.p, pt.p);
    int ok = status == want_status && out_guards(&pt);
    ok &= in_done(&i);
    note(dec, ok, file, name);
    if (status != 0 || want_status != 0) {
        out_free(&pt);
        return ok;
    }
    input q = in_bytes(pt.p, pn);
    output o = out_new(bn);
    status = CALL(comp, q.p, o.p);
    int ok2 = status == 0 && out_guards(&o) && memcmp(o.p, want, bn) == 0;
    ok2 &= in_done(&q);
    out_free(&o);
    out_free(&pt);
    return note(comp, ok2, file, name) && ok;
}

/* A G1 point from its compressed form, through crypto_bls_g1_decode. */
static int g1_point(const uint8_t *b, uint8_t point[G1_POINT]) {
    input i = in_bytes(b, 48);
    output pt = out_new(G1_POINT);
    int ok = CALL(F_BLS_G1_DECODE, i.p, pt.p) == 0 && out_guards(&pt);
    memcpy(point, pt.p, G1_POINT);
    ok &= in_done(&i);
    out_free(&pt);
    return ok;
}

/* The compressed form of a G1 point, through crypto_bls_g1_compress, against want. */
static int g1_compressed_is(const uint8_t point[G1_POINT], const uint8_t *want) {
    input q = in_bytes(point, G1_POINT);
    output o = out_new(48);
    int ok = CALL(F_BLS_G1_COMPRESS, q.p, o.p) == 0 && out_guards(&o) && memcmp(o.p, want, 48) == 0;
    ok &= in_done(&q);
    out_free(&o);
    return ok;
}

static int case_bls_g1_add(cursor *c, const char *name) {
    const uint8_t *a = take(c, 48), *b = take(c, 48), *want = take(c, 48);
    uint8_t pa[G1_POINT], pb[G1_POINT];
    int ok = g1_point(a, pa) && g1_point(b, pb);
    input x = in_bytes(pa, G1_POINT), y = in_bytes(pb, G1_POINT);
    output o = out_new(G1_POINT);
    ok &= CALL(F_BLS_G1_ADD, x.p, y.p, o.p) == 0 && out_guards(&o) && g1_compressed_is(o.p, want);
    ok &= in_done(&x) & in_done(&y);
    out_free(&o);
    return note(F_BLS_G1_ADD, ok, c->name, name);
}

static int case_bls_g1_neg(cursor *c, const char *name) {
    const uint8_t *a = take(c, 48), *want = take(c, 48);
    uint8_t pa[G1_POINT];
    int ok = g1_point(a, pa);
    input x = in_bytes(pa, G1_POINT);
    output o = out_new(G1_POINT);
    ok &= CALL(F_BLS_G1_NEG, x.p, o.p) == 0 && out_guards(&o) && g1_compressed_is(o.p, want);
    ok &= in_done(&x);
    out_free(&o);
    return note(F_BLS_G1_NEG, ok, c->name, name);
}

/* expand_message_xmd: length is checked first, then scratch, then the output. */
static int case_bls_xmd(cursor *c, const char *name) {
    blob msg = take_blob(c), dst = take_blob(c);
    uint64_t length = take64(c), want_status = take64(c);
    blob want = take_blob(c);
    uint8_t len8[8];
    wr64(len8, length);
    size_t out_size = (size_t)(24 + (want_status == 0 ? length : 0));
    int ok = 1;
    for (int small = 0; small < 3; small++) {
        if (small && want_status != 0) break;
        input m = in_list(msg.p, msg.n), d = in_list(dst.p, dst.n), l = in_bytes(len8, 8);
        output s = out_sized((size_t)(H2C_SCRATCH + msg.n + dst.n - (small == 1))), o = out_sized(out_size - (small == 2));
        uint64_t status = CALL(F_BLS_XMD, m.p, d.p, l.p, s.p, o.p);
        if (small)
            ok &= status == BUFFER_TOO_SMALL && out_guards(&s) && out_guards(&o);
        else if (want_status != 0)
            ok &= status == want_status && out_guards(&s) && out_guards(&o);
        else
            ok &= status == 0 && out_guards(&s) && want.n == length && out_list_is(&o, want.p, want.n);
        ok &= in_done(&m) & in_done(&d) & in_done(&l);
        out_free(&s);
        out_free(&o);
    }
    return note(F_BLS_XMD, ok, c->name, name);
}

static int case_bls_hash_to_g2(cursor *c, const char *name) {
    blob msg = take_blob(c), dst = take_blob(c);
    uint64_t want_status = take64(c);
    const uint8_t *want = take(c, 192);
    int ok = 1;
    for (int small = 0; small < 2; small++) {
        input m = in_list(msg.p, msg.n), d = in_list(dst.p, dst.n);
        output s = out_sized((size_t)(H2C_SCRATCH + msg.n + dst.n - small)), o = out_new(192);
        uint64_t status = CALL(F_BLS_HASH_TO_G2, m.p, d.p, s.p, o.p);
        if (small)
            ok &= status == BUFFER_TOO_SMALL && out_guards(&s) && out_guards(&o);
        else
            ok &= status == want_status && out_guards(&s) && out_guards(&o) &&
                  (want_status != 0 || memcmp(o.p, want, 192) == 0);
        ok &= in_done(&m) & in_done(&d);
        out_free(&s);
        out_free(&o);
    }
    return note(F_BLS_HASH_TO_G2, ok, c->name, name);
}

/* ---------------------------------------------------------------- KZG */

#define KZG_SCRATCH 2097152      /* include/kzg.inc */
#define KZG_PER_ENTRY 8192
#define KZG_SETTINGS 1198368
#define KZG_BLOB 131072
#define KZG_CELLS 262144
#define KZG_PROOFS 6144

/* The settings of the last setup case that decoded, which the other KZG cases read. */
static uint8_t *kzg_settings;

/* TrustedSetup.ofBytes: on success the decoded setup becomes the settings of the cases after it. */
static int case_kzg_setup(cursor *c, const char *name) {
    blob l = take_blob(c), m = take_blob(c), g = take_blob(c);
    uint64_t want = take64(c);
    input a = in_list(l.p, l.n), b = in_list(m.p, m.n), d = in_list(g.p, g.n);
    output o = out_new(KZG_SETTINGS);
    uint64_t status = CALL(F_KZG_SETUP, a.p, b.p, d.p, o.p);
    int ok = status == want && out_guards(&o);
    ok &= in_done(&a) & in_done(&b) & in_done(&d);
    if (ok && status == 0) {
        free(kzg_settings);
        kzg_settings = xmalloc(KZG_SETTINGS);
        memcpy(kzg_settings, o.p, KZG_SETTINGS);
    }
    out_free(&o);
    return note(F_KZG_SETUP, ok, c->name, name);
}

/*
 * One KZG call, with the exact scratch and with one byte less, which must give
 * CRYPTO_BUFFER_TOO_SMALL: every KZG function checks scratch first. args holds
 * the inputs, with NULL where the scratch and the outputs go; sizes gives the
 * size of each output, in order. With want_status 0, outputs must hold want,
 * one after another.
 */
static int kzg_run(int fn, const void **args, size_t nargs, size_t entries, const size_t *sizes, size_t nout,
                   uint64_t want_status, const uint8_t *want) {
    int ok = 1;
    for (int small = 0; small < 2; small++) {
        output s = out_sized((size_t)(KZG_SCRATCH + KZG_PER_ENTRY * entries - small)), o[2];
        const void *a[7];
        for (size_t i = 0; i < nargs; i++) a[i] = args[i];
        a[nargs - nout - 1] = s.p;                  /* the scratch, then the outputs, last */
        for (size_t j = 0; j < nout; j++) {
            o[j] = out_new(sizes[j]);
            a[nargs - nout + j] = o[j].p;
        }
        uint64_t status = checked_call(fn, a, nargs);
        if (small)
            ok &= status == BUFFER_TOO_SMALL;
        else
            ok &= status == want_status;
        ok &= out_guards(&s);
        size_t at = 0;
        for (size_t j = 0; j < nout; j++) {
            ok &= out_guards(&o[j]);
            if (!small && want_status == 0) ok &= memcmp(o[j].p, want + at, sizes[j]) == 0;
            at += sizes[j];
            out_free(&o[j]);
        }
        out_free(&s);
    }
    return ok;
}

static int case_kzg(cursor *c, uint64_t kind, const char *name) {
    if (!kzg_settings && kind != K_KZG_CHALLENGE && kind != K_KZG_CELLS && kind != K_KZG_CELL_CHALLENGE) {
        fprintf(stderr, "%s: %s: no trusted setup before it\n", c->name, name);
        exit(2);
    }
    input set = in_bytes(kzg_settings ? kzg_settings : (const uint8_t *)"", kzg_settings ? KZG_SETTINGS : 1);
    input in[5];
    size_t nin = 0;
    int fn, ok;
    uint64_t st;
    const uint8_t *want;
    if (kind == K_KZG_COMMIT) {
        in[nin++] = in_bytes(take(c, KZG_BLOB), KZG_BLOB);
        st = take64(c), want = take(c, 48);
        size_t sz[] = {48};
        const void *a[] = {set.p, in[0].p, NULL, NULL};
        ok = kzg_run(fn = F_KZG_COMMIT, a, 4, 0, sz, 1, st, want);
    } else if (kind == K_KZG_PROOF) {
        in[nin++] = in_bytes(take(c, KZG_BLOB), KZG_BLOB);
        in[nin++] = in_bytes(take(c, 32), 32);
        st = take64(c), want = take(c, 80);
        size_t sz[] = {48, 32};
        const void *a[] = {set.p, in[0].p, in[1].p, NULL, NULL, NULL};
        ok = kzg_run(fn = F_KZG_PROOF, a, 6, 0, sz, 2, st, want);
    } else if (kind == K_KZG_VERIFY) {
        in[nin++] = in_bytes(take(c, 48), 48);
        in[nin++] = in_bytes(take(c, 32), 32);
        in[nin++] = in_bytes(take(c, 32), 32);
        in[nin++] = in_bytes(take(c, 48), 48);
        st = take64(c);
        uint8_t v[8];
        wr64(v, take64(c));
        size_t sz[] = {8};
        const void *a[] = {set.p, in[0].p, in[1].p, in[2].p, in[3].p, NULL, NULL};
        ok = kzg_run(fn = F_KZG_VERIFY, a, 7, 0, sz, 1, st, v);
    } else if (kind == K_KZG_BLOB_PROOF) {
        in[nin++] = in_bytes(take(c, KZG_BLOB), KZG_BLOB);
        in[nin++] = in_bytes(take(c, 48), 48);
        st = take64(c), want = take(c, 48);
        size_t sz[] = {48};
        const void *a[] = {set.p, in[0].p, in[1].p, NULL, NULL};
        ok = kzg_run(fn = F_KZG_BLOB_PROOF, a, 5, 0, sz, 1, st, want);
    } else if (kind == K_KZG_BLOB_VERIFY) {
        in[nin++] = in_bytes(take(c, KZG_BLOB), KZG_BLOB);
        in[nin++] = in_bytes(take(c, 48), 48);
        in[nin++] = in_bytes(take(c, 48), 48);
        st = take64(c);
        uint8_t v[8];
        wr64(v, take64(c));
        size_t sz[] = {8};
        const void *a[] = {set.p, in[0].p, in[1].p, in[2].p, NULL, NULL};
        ok = kzg_run(fn = F_KZG_BLOB_VERIFY, a, 6, 0, sz, 1, st, v);
    } else if (kind == K_KZG_BLOB_BATCH) {
        blob b = take_blob(c), cm = take_blob(c), pr = take_blob(c);
        in[nin++] = in_entries(b, KZG_BLOB);
        in[nin++] = in_entries(cm, 48);
        in[nin++] = in_entries(pr, 48);
        st = take64(c);
        uint8_t v[8];
        wr64(v, take64(c));
        size_t sz[] = {8};
        const void *a[] = {set.p, in[0].p, in[1].p, in[2].p, NULL, NULL};
        ok = kzg_run(fn = F_KZG_BLOB_BATCH, a, 6, (size_t)(b.n / KZG_BLOB), sz, 1, st, v);
    } else if (kind == K_KZG_CHALLENGE) {
        in[nin++] = in_bytes(take(c, KZG_BLOB), KZG_BLOB);
        in[nin++] = in_bytes(take(c, 48), 48);
        st = take64(c), want = take(c, 32);
        size_t sz[] = {32};
        const void *a[] = {in[0].p, in[1].p, NULL, NULL};
        ok = kzg_run(fn = F_KZG_CHALLENGE, a, 4, 0, sz, 1, st, want);
    } else if (kind == K_KZG_CELLS) {
        in[nin++] = in_bytes(take(c, KZG_BLOB), KZG_BLOB);
        st = take64(c), want = take(c, KZG_CELLS);
        size_t sz[] = {KZG_CELLS};
        const void *a[] = {in[0].p, NULL, NULL};
        ok = kzg_run(fn = F_KZG_CELLS, a, 3, 0, sz, 1, st, want);
    } else if (kind == K_KZG_CELLS_PROOFS) {
        in[nin++] = in_bytes(take(c, KZG_BLOB), KZG_BLOB);
        st = take64(c), want = take(c, KZG_CELLS + KZG_PROOFS);
        size_t sz[] = {KZG_CELLS, KZG_PROOFS};
        const void *a[] = {set.p, in[0].p, NULL, NULL, NULL};
        ok = kzg_run(fn = F_KZG_CELLS_PROOFS, a, 5, 0, sz, 2, st, want);
    } else if (kind == K_KZG_CELL_BATCH) {
        blob cm = take_blob(c), ix = take_blob(c), ce = take_blob(c), pr = take_blob(c);
        in[nin++] = in_entries(cm, 48);
        in[nin++] = in_entries(ix, 8);
        in[nin++] = in_entries(ce, 2048);
        in[nin++] = in_entries(pr, 48);
        st = take64(c);
        uint8_t v[8];
        wr64(v, take64(c));
        size_t sz[] = {8};
        const void *a[] = {set.p, in[0].p, in[1].p, in[2].p, in[3].p, NULL, NULL};
        ok = kzg_run(fn = F_KZG_CELL_BATCH, a, 7, (size_t)(cm.n / 48), sz, 1, st, v);
    } else if (kind == K_KZG_RECOVER) {
        blob ix = take_blob(c), ce = take_blob(c);
        in[nin++] = in_entries(ix, 8);
        in[nin++] = in_entries(ce, 2048);
        st = take64(c), want = take(c, KZG_CELLS + KZG_PROOFS);
        size_t sz[] = {KZG_CELLS, KZG_PROOFS};
        const void *a[] = {set.p, in[0].p, in[1].p, NULL, NULL, NULL};
        ok = kzg_run(fn = F_KZG_RECOVER, a, 6, 0, sz, 2, st, want);
    } else {
        blob cm = take_blob(c), ci = take_blob(c), ix = take_blob(c), ce = take_blob(c), pr = take_blob(c);
        in[nin++] = in_entries(cm, 48);
        in[nin++] = in_entries(ci, 8);
        in[nin++] = in_entries(ix, 8);
        in[nin++] = in_entries(ce, 2048);
        in[nin++] = in_entries(pr, 48);
        st = take64(c), want = take(c, 32);
        size_t sz[] = {32};
        const void *a[] = {in[0].p, in[1].p, in[2].p, in[3].p, in[4].p, NULL, NULL};
        ok = kzg_run(fn = F_KZG_CELL_CHALLENGE, a, 7, (size_t)(cm.n / 48 + ci.n / 8), sz, 1, st, want);
    }
    ok &= in_done(&set);
    for (size_t i = 0; i < nin; i++) ok &= in_done(&in[i]);
    return note(fn, ok, c->name, name);
}

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
        else if (kind == K_GCM) ok = case_aead(c, name, F_GCM_AE, F_GCM_AD, 16);
        else if (kind == K_CHACHA) ok = case_aead(c, name, F_CHACHA_ENC, F_CHACHA_DEC, 32);
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
        } else if (kind == K_VERIFY) ok = case_verify(c, name, F_VERIFY, 33);
        else if (kind == K_X25519) {
            const uint8_t *scalar = take(c, 32), *u = take(c, 32);
            uint64_t st = take64(c);
            ok = case_fixed(F_X25519, scalar, 32, u, 32, st, take(c, 32), 32, c->name, name);
        } else if (kind == K_P256_PUBLIC_KEY) {
            const uint8_t *priv = take(c, 32);
            uint64_t st = take64(c);
            ok = case_fixed(F_P256_PUBLIC_KEY, priv, 32, NULL, 0, st, take(c, 65), 65, c->name, name);
        } else if (kind == K_P256_ECDH) {
            const uint8_t *pub = take(c, 65), *priv = take(c, 32);
            uint64_t st = take64(c);
            ok = case_fixed(F_P256_ECDH, pub, 65, priv, 32, st, take(c, 32), 32, c->name, name);
        } else if (kind == K_P256_SIGN) {
            const uint8_t *priv = take(c, 32), *hash = take(c, 32);
            uint64_t st = take64(c);
            ok = case_fixed(F_P256_SIGN, priv, 32, hash, 32, st, take(c, 64), 64, c->name, name);
        } else if (kind == K_P256_VERIFY) ok = case_verify(c, name, F_P256_VERIFY, 65);
        else if (kind == K_POLY1305) {
            const uint8_t *key = take(c, 32);
            blob msg = take_blob(c);
            const uint8_t *want = take(c, 16);
            input k = in_bytes(key, 32), m = in_list(msg.p, msg.n);
            output t = out_new(16);
            uint64_t status = CALL(F_POLY1305_MAC, k.p, m.p, t.p);
            ok = status == 0 && out_guards(&t) && memcmp(t.p, want, 16) == 0;
            ok &= in_done(&k) & in_done(&m);
            out_free(&t);
            note(F_POLY1305_MAC, ok, c->name, name);
        }
        else if (kind == K_SHA512) ok = case_sha512(c, name);
        else if (kind == K_ED25519_PUBLIC_KEY) {
            const uint8_t *priv = take(c, 32);
            ok = case_fixed(F_ED25519_PUBLIC_KEY, priv, 32, NULL, 0, 0, take(c, 32), 32, c->name, name);
        } else if (kind == K_ED25519_SIGN) ok = case_ed25519_sign(c, name);
        else if (kind == K_ED25519_VERIFY) ok = case_ed25519_verify(c, name);
        else if (kind == K_BLS_SK_TO_PK) {
            const uint8_t *sk = take(c, 32);
            uint64_t st = take64(c);
            ok = case_fixed(F_BLS_SK_TO_PK, sk, 32, NULL, 0, st, take(c, 48), 48, c->name, name);
        } else if (kind == K_BLS_SIGN) ok = case_bls_sign(c, name);
        else if (kind == K_BLS_VERIFY) {
            const uint8_t *pk = take(c, 48);
            blob msg = take_blob(c);
            const uint8_t *sig = take(c, 96);
            uint64_t want = take64(c);
            blob one = {pk, 48};
            ok = case_bls_check(F_BLS_VERIFY, NULL, pk, msg, sig, want, c->name, name);
            ok &= case_bls_cached(one, msg, sig, want, c->name, name);
        } else if (kind == K_BLS_FAST || kind == K_BLS_ETH_FAST) {
            blob keys = take_blob(c), msg = take_blob(c);
            const uint8_t *sig = take(c, 96);
            uint64_t want = take64(c);
            ok = case_bls_check(kind == K_BLS_FAST ? F_BLS_FAST : F_BLS_ETH_FAST, &keys, NULL, msg, sig, want,
                                c->name, name);
            ok &= case_bls_cached(keys, msg, sig, want, c->name, name);
        } else if (kind == K_BLS_AGGREGATE) {
            blob sigs = take_blob(c);
            uint64_t st = take64(c);
            ok = case_bls_list(F_BLS_AGGREGATE, sigs, 96, st, take(c, 96), 96, c->name, name);
        } else if (kind == K_BLS_ETH_AGGREGATE) {
            blob keys = take_blob(c);
            uint64_t st = take64(c);
            ok = case_bls_list(F_BLS_ETH_AGGREGATE, keys, 48, st, take(c, 48), 48, c->name, name);
        } else if (kind == K_BLS_KEY_VALIDATE) {
            const uint8_t *pk = take(c, 48);
            uint8_t want[8];
            wr64(want, take64(c));
            ok = case_fixed(F_BLS_KEY_VALIDATE, pk, 48, NULL, 0, 0, want, 8, c->name, name);
            { /* crypto_bls_key_cache_fill of the key: status 1 when it is valid, else 2 */
                output kc = new_key_cache(48, 1);
                input kk = in_bytes(pk, 48);
                int fok = CALL(F_BLS_CACHE_FILL, kk.p, (const void *)(uintptr_t)0, (const void *)(uintptr_t)1, kc.p) == 0 &&
                          out_guards(&kc) && rd64(kc.p + 32) == (rd64(want) ? 1u : 2u) && memcmp(kc.p + 40, pk, 48) == 0;
                fok &= in_done(&kk);
                out_free(&kc);
                ok &= note(F_BLS_CACHE_FILL, fok, c->name, name);
            }
        } else if (kind == K_BLS_G1_DECODE) {
            const uint8_t *b = take(c, 48);
            uint64_t st = take64(c);
            ok = case_bls_decode(F_BLS_G1_DECODE, F_BLS_G1_COMPRESS, b, 48, G1_POINT, st, take(c, 48), c->name, name);
        } else if (kind == K_BLS_G2_DECODE) {
            const uint8_t *b = take(c, 96);
            uint64_t st = take64(c);
            ok = case_bls_decode(F_BLS_G2_DECODE, F_BLS_G2_COMPRESS, b, 96, G2_POINT, st, take(c, 96), c->name, name);
        } else if (kind == K_BLS_G1_ADD) ok = case_bls_g1_add(c, name);
        else if (kind == K_BLS_G1_NEG) ok = case_bls_g1_neg(c, name);
        else if (kind == K_BLS_XMD) ok = case_bls_xmd(c, name);
        else if (kind == K_BLS_HASH_TO_G2) ok = case_bls_hash_to_g2(c, name);
        else if (kind == K_KZG_SETUP) ok = case_kzg_setup(c, name);
        else if (kind > K_KZG_SETUP && kind <= K_KZG_CELL_CHALLENGE) ok = case_kzg(c, kind, name);
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
#ifdef CRYPTO_SHA_VARIANT
    if (!sha_variant_supported()) {
        printf("SKIP the sha variant: this CPU lacks its features\n");
        return 0;
    }
    printf("== the sha variant\n");
#endif
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
