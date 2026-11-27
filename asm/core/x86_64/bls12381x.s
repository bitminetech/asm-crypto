/*
 * The x variant of bls12381.s for x86-64 (bls12-381.md, The x variant): the same source with
 * CRYPTO_ADX set, so crypto_bls_fp_mul uses mulx (BMI2) and the carry chains of adcx and adox (ADX).
 * The shell runs it only on a CPU with BMI2 and ADX.
 */
.set CRYPTO_ADX, 1
.include "bls12381.s"
