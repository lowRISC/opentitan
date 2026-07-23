/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* K-PKE.Encrypt for ML-KEM-1024 (q = 3329). */

.globl mlkem1024_encrypt

.text

/**
 * K-PKE.Encrypt for ML-KEM-1024.
 *
 * Computes ciphertext c = (ct_u || ct_v) from public key ek=(t || rho), message m, and randomness r.
 *
 * @param[in] x2: DMEM address of public key t (1536 bytes)
 * @param[in] x3: DMEM address of public key rho (32 bytes)
 * @param[in] x4: DMEM address of message m (32 bytes)
 * @param[in] x5: DMEM address of randomness r (32 bytes)
 * @param[in] x6: DMEM output address for ct_u (1408 bytes)
 * @param[in] x7: DMEM output address for ct_v (160 bytes)
 *
 */
mlkem1024_encrypt:
  /* Push caller input parameters x2..x7 and working registers onto stack (48 bytes) */
  .irp reg, x2, x3, x4, x5, x6, x7, x13, x14, x16, x17, x18, x20
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* 1. Compute u[0..3] vector: u_i = INTT(sum_j A[j][i] * y_hat[j]) + e1[i] */
  lw   x13, 16-48(x31)  /* ct_u working output pointer */
  addi x16, x0, 0       /* i = 0 (row of A^T / col of A) */
  addi x18, x0, 4

_encrypt_u_outer_loop:
  /* Zero out poly_slot1 (accumulates sum_j A[j][i] * y_hat[j]) */
  la x2, poly_slot1
  li x20, 32
  bn.xor w0, w0, w0
_encrypt_zero_u_acc:
  bn.sid x0, 0(x2++)
  addi x20, x20, -1
  bne  x20, x0, _encrypt_zero_u_acc

  addi x17, x0, 0       /* j = 0 (col of A^T / row of A) */

_encrypt_u_inner_loop:
  /* Sample y[j] into poly_slot0 and apply NTT in-place */
  lw   x2, 12-48(x31)   /* randomness r address */
  la   x4, poly_slot0
  addi x3, x17, 0       /* N = j */
  jal  x1, expand_prf

  la   x2, poly_slot0
  addi x3, x2, 0
  jal  x1, ntt

  /* Scale y_hat[j] in poly_slot0 to Montgomery domain (R^1) by 2988 */
  la   x2, poly_slot0
  la   x3, keygen_scale_const_2988
  la   x4, _basemul_twiddles
  la   x5, poly_slot0
  jal  x1, poly_mul

  /* Expand A[i][j] into poly_slot2 (row=i, col=j) */
  lw   x2, 4-48(x31)    /* pk_rho */
  addi x3, x16, 0     /* row index = i */
  addi x4, x17, 0     /* col index = j */
  la   x5, poly_slot2
  jal  x1, expand_a

  /* poly_slot1 += A[j][i] * y_hat[j] */
  la   x2, poly_slot2
  la   x3, poly_slot0
  la   x4, _basemul_twiddles
  la   x5, poly_slot1
  la   x6, poly_slot1
  jal  x1, poly_mul_add

  addi x17, x17, 1
  bne  x17, x18, _encrypt_u_inner_loop

  /* INTT(poly_slot1) in-place */
  la   x2, poly_slot1
  addi x3, x2, 0
  jal  x1, intt

  /* Sample e1[i] (nonce N = 4 + i) into poly_slot0 */
  lw   x2, 12-48(x31)   /* randomness r address */
  la   x4, poly_slot0
  addi x3, x16, 4       /* N = 4 + i */
  jal  x1, expand_prf

  /* poly_slot1 += e1[i] */
  la   x2, poly_slot1
  la   x3, poly_slot0
  la   x4, poly_slot1
  jal  x1, poly_add

  /* compress_11(poly_slot1, ct_u + i * 352) */
  la   x2, poly_slot1
  addi x3, x13, 0
  jal  x1, compress_11

  addi x13, x13, 352    /* 11 bits * 256 / 8 = 352 bytes per polynomial */
  addi x16, x16, 1
  bne  x16, x18, _encrypt_u_outer_loop

  /* 2. Compute v = INTT(sum_j t_hat[j] * y_hat[j]) + e2 + decode_1(m) */
  /* Zero out poly_slot1 */
  la x2, poly_slot1
  li x20, 32
  bn.xor w0, w0, w0
_encrypt_zero_v_acc:
  bn.sid x0, 0(x2++)
  addi x20, x20, -1
  bne  x20, x0, _encrypt_zero_v_acc

  lw   x14, 0-48(x31)   /* pk_t working pointer */
  addi x17, x0, 0       /* j = 0 */
  addi x18, x0, 4

_encrypt_v_loop:
  /* Sample y[j] into poly_slot0 and apply NTT in-place */
  lw   x2, 12-48(x31)   /* randomness r address */
  la   x4, poly_slot0
  addi x3, x17, 0       /* N = j */
  jal  x1, expand_prf

  la   x2, poly_slot0
  addi x3, x2, 0
  jal  x1, ntt

  /* Scale y_hat[j] in poly_slot0 to Montgomery domain (R^1) by 2988 */
  la   x2, poly_slot0
  la   x3, keygen_scale_const_2988
  la   x4, _basemul_twiddles
  la   x5, poly_slot0
  jal  x1, poly_mul

  /* decode_12(t_bytes[j], poly_slot2) */
  addi x2, x14, 0
  la   x3, poly_slot2
  jal  x1, decode_12

  /* poly_slot1 += t_hat[j] * y_hat[j] */
  la   x2, poly_slot2
  la   x3, poly_slot0
  la   x4, _basemul_twiddles
  la   x5, poly_slot1
  la   x6, poly_slot1
  jal  x1, poly_mul_add

  addi x14, x14, 384    /* 12 bits * 256 / 8 = 384 bytes */
  addi x17, x17, 1
  bne  x17, x18, _encrypt_v_loop

  /* INTT(poly_slot1) in-place */
  la   x2, poly_slot1
  addi x3, x2, 0
  jal  x1, intt

  /* Sample e2 (nonce N = 8) into poly_slot0 */
  lw   x2, 12-48(x31)   /* randomness r address */
  la   x4, poly_slot0
  addi x3, x0, 8        /* N = 8 */
  jal  x1, expand_prf

  /* poly_slot1 += e2 */
  la   x2, poly_slot1
  la   x3, poly_slot0
  la   x4, poly_slot1
  jal  x1, poly_add

  /* Decode message m: decode_1(m) into poly_slot0 */
  lw   x2, 8-48(x31)   /* message m address */
  la   x3, poly_slot0
  jal  x1, decode_1

  /* decompress_1: mu = m * 1665 */
  la   x4, poly_slot0
  li   x20, 1665
  loopi 256, 4
    lw   x21, 0(x4)
    beq  x21, x0, 1f
    addi x21, x20, 0
1:
    sw   x21, 0(x4)
    addi x4, x4, 4
    /* End of loop */

  /* poly_slot1 += mu */
  la   x2, poly_slot1
  la   x3, poly_slot0
  la   x4, poly_slot1
  jal  x1, poly_add

  /* compress_5(poly_slot1, ct_v) */
  la   x2, poly_slot1
  lw   x3, 20-48(x31)   /* ct_v output address */
  jal  x1, compress_5

  /* Restore stack and return */
  .irp reg, x20, x18, x17, x16, x14, x13, x7, x6, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr
  ret
