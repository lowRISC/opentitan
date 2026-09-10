/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* K-PKE.Encrypt for ML-KEM-1024 (q = 3329). */

.globl mlkem1024_encrypt
.globl mlkem1024_encrypt_uncompressed

.text

/**
 * K-PKE.Encrypt for ML-KEM-1024 (FIPS 203 Algorithm 14 K-PKE.Encrypt).
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
 * Clobbered WDRs: w0, w1, w2, w3, w4, w5, w6, w10, w29, w30, w31.
 */
mlkem1024_encrypt:
  addi x8, x0, 0
  jal  x0, _encrypt_core

mlkem1024_encrypt_uncompressed:
  addi x8, x0, 1

_encrypt_core:
  /* Push caller input parameters x2..x7 and working registers onto stack (44 bytes) */
  .irp reg, x2, x3, x4, x5, x6, x7, x13, x14, x16, x17, x18
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  addi x18, x8, 0     /* x18 = mode flag (0 = compressed, 1 = uncompressed) */
  addi x19, x2, 0     /* x19 = pk_t address */
  addi x23, x3, 0     /* x23 = pk_rho address */
  addi x15, x4, 0     /* x15 = message m address */
  addi x26, x5, 0     /* x26 = randomness r address */
  addi x27, x6, 0     /* x27 = ct_u / u_out address */
  addi x21, x7, 0     /* x21 = ct_v / v_out address */

  /* Initialize keygen_scale_const_2988 in DMEM with constant 2988 (0x0bac) */
  la     x2, const_2988_wdr
  addi   x10, x0, 0
  bn.lid x10, 0(x2)
  la     x2, keygen_scale_const_2988
  loopi  32, 1
    bn.sid x10, 0(x2++)
    /* End of loop */

  /* Pre-sample y[j], NTT transform, and pre-scale to Montgomery domain in poly_slot_y_hat */
  la   x14, poly_slot_y_hat
  addi x17, x0, 0       /* j = 0 */

  loopi 4, 19
    addi x2, x26, 0     /* randomness r address */
    la   x4, poly_slot0
    addi x3, x17, 0       /* N = j */
    jal  x1, expand_prf

    la   x2, poly_slot0
    addi x3, x2, 0
    jal  x1, ntt

    /* Scale y_hat[j] in poly_slot0 to Montgomery domain (R^1) by 2988 and store in poly_slot_y_hat + j * 1024 */
    la   x2, poly_slot0
    la   x3, keygen_scale_const_2988
    la   x4, _basemul_twiddles
    addi x5, x14, 0
    jal  x1, poly_mul

    addi x14, x14, 1024
    addi x17, x17, 1
    /* End of loop */

  /* 1. Compute u[0..3] vector: u_i = INTT(sum_j A[j][i] * y_hat[j]) + e1[i] */
  addi x13, x27, 0     /* ct_u / u_out working output pointer */
  addi x16, x0, 0       /* i = 0 (col of A / row of A^T) */

  loopi 4, 59
    /* Zero out poly_slot1 (accumulates sum_j A[j][i] * y_hat[j]) */
    la x2, poly_slot1
    bn.xor w0, w0, w0
    loopi 32, 1
      bn.sid x0, 0(x2++)
      /* End of loop */

    addi x17, x0, 0       /* j = 0 (row of A / col of A^T) */

    loopi 4, 21
      /* Expand A[j][i] into poly_slot2 (row=j, col=i) */
      addi x2, x23, 0     /* pk_rho */
      addi x3, x16, 0     /* col index = i */
      addi x4, x17, 0     /* row index = j */
      la   x5, poly_slot2
      jal  x1, expand_a

      /* poly_slot1 += A[j][i] * y_hat[j] */
      la   x2, poly_slot2
      la   x3, poly_slot_y_hat
      slli x7, x17, 10    /* j * 1024 */
      add  x3, x3, x7
      la   x4, _basemul_twiddles
      la   x5, poly_slot1
      la   x6, poly_slot1
      jal  x1, poly_mul_add

      addi x17, x17, 1
      /* End of loop */

    /* INTT(poly_slot1) in-place */
    la   x2, poly_slot1
    addi x3, x2, 0
    jal  x1, intt

    /* Sample e1[i] (nonce N = 4 + i) into poly_slot0 */
    addi x2, x26, 0     /* randomness r address */
    la   x4, poly_slot0
    addi x3, x16, 4       /* N = 4 + i */
    jal  x1, expand_prf

    /* poly_slot1 += e1[i] */
    la   x2, poly_slot1
    la   x3, poly_slot0
    la   x4, poly_slot1
    jal  x1, poly_add

    /* Check mode x18: 1 = uncompressed, otherwise compressed */
    li   x24, 1
    bne  x18, x24, _encrypt_compress_u
    /* Uncompressed mode: copy 1024 bytes of poly_slot1 into u_out[i] */
    la   x2, poly_slot1
    addi x3, x13, 0
    loopi 32, 2
      bn.lid x0, 0(x2++)
      bn.sid x0, 0(x3++)
    addi x13, x13, 1024
    jal  x0, _encrypt_u_next

_encrypt_compress_u:
    /* Compressed mode: compress_11(poly_slot1, ct_u + i * 352) */
    la   x2, poly_slot1
    addi x3, x13, 0
    jal  x1, compress_11
    addi x13, x13, 352

_encrypt_u_next:
    addi x16, x16, 1
    /* End of loop */

  /* 2. Compute v = INTT(sum_j t_hat[j] * y_hat[j]) + e2 + decode_1(m) */
  /* Zero out poly_slot1 */
  la x2, poly_slot1
  bn.xor w0, w0, w0
  loopi 32, 1
    bn.sid x0, 0(x2++)
    /* End of loop */

  addi x14, x19, 0     /* pk_t working pointer */
  addi x17, x0, 0       /* j = 0 */

  loopi 4, 20
    /* decode_12(t_bytes[j], poly_slot2) */
    addi x2, x14, 0
    la   x3, poly_slot2
    jal  x1, decode_12

    /* poly_slot1 += t_hat[j] * y_hat[j] */
    la   x2, poly_slot2
    la   x3, poly_slot_y_hat
    slli x7, x17, 10    /* j * 1024 */
    add  x3, x3, x7
    la   x4, _basemul_twiddles
    la   x5, poly_slot1
    la   x6, poly_slot1
    jal  x1, poly_mul_add

    addi x14, x14, 384    /* 12 bits * 256 / 8 = 384 bytes */
    addi x17, x17, 1
    /* End of loop */

  /* INTT(poly_slot1) in-place */
  la   x2, poly_slot1
  addi x3, x2, 0
  jal  x1, intt

  /* Sample e2 (nonce N = 8) into poly_slot0 */
  addi x2, x26, 0     /* randomness r address */
  la   x4, poly_slot0
  addi x3, x0, 8        /* N = 8 */
  jal  x1, expand_prf

  /* poly_slot1 += e2 */
  la   x2, poly_slot1
  la   x3, poly_slot0
  la   x4, poly_slot1
  jal  x1, poly_add

  /* Decode message m: decode_1(m) into poly_slot0 (already decompressed to mu = m * 1665) */
  addi x2, x15, 0     /* message m address */
  la   x3, poly_slot0
  jal  x1, decode_1

  /* poly_slot1 += mu */
  la   x2, poly_slot1
  la   x3, poly_slot0
  la   x4, poly_slot1
  jal  x1, poly_add

  /* Check mode x18: 1 = uncompressed, otherwise compressed */
  li   x24, 1
  bne  x18, x24, _encrypt_compress_v
  /* Uncompressed mode: copy 1024 bytes of poly_slot1 into v_out */
  la  x2, poly_slot1
  addi x3, x21, 0     /* v_out output address */
  loopi 32, 2
    bn.lid x0, 0(x2++)
    bn.sid x0, 0(x3++)
  jal x0, _encrypt_v_done

_encrypt_compress_v:
  /* Compressed mode: compress_5(poly_slot1, ct_v) */
  la   x2, poly_slot1
  addi x3, x21, 0     /* ct_v output address */
  jal  x1, compress_5

_encrypt_v_done:

  /* Restore stack and return */
  .irp reg, x18, x17, x16, x14, x13, x7, x6, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr
  ret
