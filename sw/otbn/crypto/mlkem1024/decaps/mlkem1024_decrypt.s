/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-KEM-1024 Decryption OTBN application (FIPS 203 Algorithm 15 K-PKE.Decrypt). */

.globl mlkem1024_decrypt

.text

/**
 * K-PKE.Decrypt for ML-KEM-1024.
 *
 * Decrypts ciphertext (ct_u || ct_v) using secret key s into message m'.
 *
 * @param[in] x2: DMEM address of ct_u (1408 bytes)
 * @param[in] x3: DMEM address of ct_v (160 bytes)
 * @param[in] x4: DMEM address of secret key s (1536 bytes)
 * @param[in] x5: DMEM output address for message m' (32 bytes)
 *
 */
mlkem1024_decrypt:
  /* Push caller input parameters x2..x5 and working registers onto stack (40 bytes) */
  .irp reg, x2, x3, x4, x5, x7, x10, x14, x15, x16, x17
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Initialize keygen_scale_const_2988 in DMEM with scalar 16-bit [2988, 0, ...] */
  la    x2, keygen_scale_const_2988
  li    x10, 2988
  loopi 4, 3
    sw   x10, 0(x2)
    sw   x0,  4(x2)
    addi x2,  x2, 8
    /* End of loop */
  la    x2, keygen_scale_const_2988
  addi  x10, x0, 0
  bn.lid x10, 0(x2)
  li    x7, 32
_init_decrypt_scale_const_loop:
  bn.sid x10, 0(x2++)
  addi  x7, x7, -1
  bne   x7, x0, _init_decrypt_scale_const_loop

  /* 1. Decompress u[0..3] from ct_u, convert to NTT, store in vector_u */
  lw   x14, 0-40(x31)  /* ct_u */
  la   x15, vector_u
  addi x16, x0, 0
  addi x17, x0, 4

_decrypt_decompress_u_loop:
  addi x2, x14, 0
  la   x3, poly_slot0
  jal  x1, decompress_11

  la   x2, poly_slot0
  la   x3, poly_slot0
  jal  x1, ntt

  /* Scale u_hat[i] in poly_slot0 to Montgomery domain (R^1) by 2988 */
  la   x2, poly_slot0
  la   x3, keygen_scale_const_2988
  la   x4, _basemul_twiddles
  la   x5, poly_slot0
  jal  x1, poly_mul

  /* Copy NTT u[i] into vector_u[i] (1024 bytes) */
  la   x2, poly_slot0
  addi x3, x15, 0
  loopi 32, 2
    bn.lid x0, 0(x2++)
    bn.sid x0, 0(x3++)
    /* End of loop */

  addi x14, x14, 352  /* 11 bits * 256 / 8 = 352 bytes per polynomial */
  addi x15, x15, 1024
  addi x16, x16, 1
  bne  x16, x17, _decrypt_decompress_u_loop

  /* 2. Decode secret key s[0..3] from sk_s into vector_s */
  lw   x14, 8-40(x31) /* sk_s */
  la   x15, vector_s
  addi x16, x0, 0
  addi x17, x0, 4

_decrypt_decode_s_loop:
  addi x2, x14, 0
  la   x3, poly_slot0
  jal  x1, decode_12

  /* Copy s[i] into vector_s[i] (1024 bytes) */
  la   x2, poly_slot0
  addi x3, x15, 0
  loopi 32, 2
    bn.lid x0, 0(x2++)
    bn.sid x0, 0(x3++)
    /* End of loop */

  addi x14, x14, 384  /* 12 bits * 256 / 8 = 384 bytes per polynomial */
  addi x15, x15, 1024
  addi x16, x16, 1
  bne  x16, x17, _decrypt_decode_s_loop

  /* 3. Compute inner product s^T * u = sum_{i=0..3} (vector_s[i] * vector_u[i]) into poly_slot2 */
  la   x2, poly_slot2
  bn.xor w0, w0, w0
  loopi 32, 1
    bn.sid x0, 0(x2++)
    /* End of loop */

  addi x16, x0, 0     /* i = 0 */
  addi x17, x0, 4

_decrypt_inner_product_loop:
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
  bne  x16, x17, _decrypt_inner_product_loop

  /* 4. INTT(s^T * u) */
  la   x2, poly_slot2
  la   x3, poly_slot2
  jal  x1, intt

  /* Decompress v from ct_v and compute w = v - INTT(s^T * u) */
  lw   x2, 4-40(x31)   /* ct_v */
  la   x3, poly_slot0
  jal  x1, decompress_5

  la   x2, poly_slot0
  la   x3, poly_slot2
  la   x4, poly_slot1
  jal  x1, poly_sub

  /* 5. Compress w to 256 bits, then encode into 32 packed bytes (m') */
  la   x2, poly_slot1
  la   x3, poly_slot0
  jal  x1, compress_1

  la   x2, poly_slot0
  lw   x3, 12-40(x31)  /* output m' address */
  jal  x1, encode_1

  /* Restore stack and return */
  .irp reg, x17, x16, x15, x14, x10, x7, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr
  ret
