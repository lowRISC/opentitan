/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-KEM-1024 Decryption OTBN application (FIPS 203 Algorithm 15 K-PKE.Decrypt). */

.globl mlkem1024_decrypt

.text

/**
 * K-PKE.Decrypt for ML-KEM-1024 (FIPS 203 Algorithm 15 K-PKE.Decrypt).
 *
 * Decrypts ciphertext (ct_u || ct_v) using secret key s into message m'.
 * Uses vectorized WDR load/store for scaling constant setup and in-place NTT/INTT transformations.
 *
 * @param[in] x2: DMEM address of ct_u (1408 bytes)
 * @param[in] x3: DMEM address of ct_v (160 bytes)
 * @param[in] x4: DMEM address of secret key s (1536 bytes)
 * @param[in] x5: DMEM output address for message m' (32 bytes)
 *
 * Clobbered WDRs: w0, w1, w2, w3, w4, w5, w6, w10, w29, w30, w31.
 */
mlkem1024_decrypt:
  /* Push caller input parameters x2..x5 and working registers onto stack (36 bytes) */
  .irp reg, x2, x3, x4, x5, x7, x10, x14, x15, x16
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  addi x18, x2, 0     /* x18 = ct_u */
  addi x19, x3, 0     /* x19 = ct_v */
  addi x20, x4, 0     /* x20 = sk_s */
  addi x21, x5, 0     /* x21 = out_m */

  /* Initialize keygen_scale_const_2988 in DMEM with constant 2988 (0x0bac) */
  la     x2, const_2988_wdr
  addi   x10, x0, 0
  bn.lid x10, 0(x2)
  la     x2, keygen_scale_const_2988
  loopi  32, 1
    bn.sid x10, 0(x2++)

  /* 1. Decompress u[0..3] from ct_u, convert to NTT, store in vector_u */
  addi x14, x18, 0  /* ct_u */
  la   x15, vector_u
  addi x16, x0, 0

  loopi 4, 20
    addi x2, x14, 0
    la   x3, poly_slot0
    jal  x1, decompress_11

    la   x2, poly_slot0
    la   x3, poly_slot0
    jal  x1, ntt

    /* Scale u_hat[i] in poly_slot0 to Montgomery domain (R^1) by 2988 directly into vector_u[i] */
    la   x2, poly_slot0
    la   x3, keygen_scale_const_2988
    la   x4, _basemul_twiddles
    addi x5, x15, 0
    jal  x1, poly_mul

    addi x14, x14, 352  /* 11 bits * 256 / 8 = 352 bytes per polynomial */
    addi x15, x15, 1024
    addi x16, x16, 1
    /* End of loop */

  /* 2. Decode secret key s[0..3] from sk_s directly into vector_s */
  addi x14, x20, 0 /* sk_s */
  la   x15, vector_s
  addi x16, x0, 0

  loopi 4, 6
    addi x2, x14, 0
    addi x3, x15, 0
    jal  x1, decode_12

    addi x14, x14, 384  /* 12 bits * 256 / 8 = 384 bytes per polynomial */
    addi x15, x15, 1024
    addi x16, x16, 1
    /* End of loop */

  /* 3. Compute inner product s^T * u = sum_{i=0..3} (vector_s[i] * vector_u[i]) into poly_slot2 */
  la   x2, poly_slot2
  bn.xor w0, w0, w0
  loopi 32, 1
    bn.sid x0, 0(x2++)
    /* End of loop */

  addi x16, x0, 0     /* i = 0 */

  loopi 4, 15
    la   x2, vector_s
    slli x7, x16, 10
    add  x2, x2, x7
    la   x3, vector_u
    add  x3, x3, x7
    la   x4, _basemul_twiddles
    la   x5, poly_slot2
    la   x6, poly_slot2
    jal  x1, poly_mul_add

    addi x16, x16, 1
    /* End of loop */

  /* 4. INTT(s^T * u) */
  la   x2, poly_slot2
  la   x3, poly_slot2
  jal  x1, intt

  /* Decompress v from ct_v and compute w = v - INTT(s^T * u) */
  addi x2, x19, 0   /* ct_v */
  la   x3, poly_slot0
  jal  x1, decompress_5

  la   x2, poly_slot0
  la   x3, poly_slot2
  la   x4, poly_slot1
  jal  x1, poly_sub

  /* 5. Compress w to 256 bits, then encode into 32 packed bytes (m') */
  la   x2, poly_slot1
  jal  x1, compress_1

  la   x2, poly_slot1
  addi x3, x21, 0  /* output m' address */
  jal  x1, encode_1

  /* Restore stack and return */
  .irp reg, x16, x15, x14, x10, x7, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr
  ret
