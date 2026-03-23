/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* High-level operations for the ML-DSA-87 verify function. */

.globl decode_sig
.globl check_infinity_norm_z
.globl compute_w_approx

.text

/**
 * Decode the signature blob.
 *
 * The signature comprises the challenge string C_TILDE, the signature
 * vector Z and the hint vector H. This routine decodes Z to polynomials in the
 * canonical representation and H to an intermediate internal representation
 * (see `decode_z` and `decode_h`). This is an implementation of the `sigDecode`
 * function (Algorithm 27) of FIPS-204.
 *
 * @param[in] x2: DMEM address of the encoded H (83 bytes in 96-byte region).
 * @param[in] x3: DMEM address of the decoded H (336 bytes in 352-byte region).
 * @param[in] x4: DMEM address of the encoded signature vector Z.
 * @param[in] x5: DMEM address of the decoded signature vector Z.
 */
sig_decode:

  /*
   * Part 1: Decode the encoded hint vector H to an internal representation in
   * in which every of the 83 bytes reside in separate 32-bit words and a
   * zero 32-bit word is inserted after the 75th element.
   */

  /* Init counter and bound to check when the 75th iteration is reached and a
     0-word has to be inserted. */
  addi x8, x0, 0
  addi x9, x0, 75

  /* Iterate over all 83 elements in 21 4-element steps. */
  loopi 21, 11
    lw x6, 0(x2)
    loopi 4, 8
      /* Only insert the 0-word after the 75th element. */
      bne x8, x9, _sig_decode_zero_insert_skip
      sw x0, 0(x3)
      addi x3, x3, 4

_sig_decode_zero_insert_skip:

      /* Rotate out the least-significant byte and store it in DMEM. */
      and  x7, x6, 0xff
      sw   x7, 0(x3)
      srli x6, x6, 8
      addi x3, x3, 4

      addi x8, x8, 1
      /* End of loop */
    addi x2, x2, 4
    /* End of loop */

  /*
   * Part 2: Decode the 7 signature polynomials Z[i] to the canonical
   * representation.
   */

  loopi 7, 5
    addi x2, x4, 0
    addi x3, x5, 0
    jal x1, decode_z

    addi x4, x4, 640
    addi x5, x5, 1024
    /* End of loop */

  ret

/**
 * Check that |Z|_inf < GAMMA - BETA = 2^19 - 120.
 *
 * This check is part of the signature verification function of ML-DSA-87.
 * The polynomial vector z is assumed to be provided in encoded form and is
 * decoded on-the-fly.
 *
 * @param[in] x2: DMEM address of the vector Z (8 * 1024 bytes).
 * @param[in] x3: DMEM address of the bound vector (32 bytes).
 * @param[out] w0: 2^256-1 if |Z|_inf < GAMMA1 - BETA, else 0.
 */
check_infinity_norm_z:
  /* Init flag. w16 is not clobbered by `check_infinity_norm`. */
  bn.subi w16, w31, 1

  /* Iterate over all Z polynomials. */
  loopi 7, 3
    jal x1, check_infinity_norm

    bn.and w16, w16, w0
    addi x2, x2, 1024
    /* End of loop */

  bn.mov w0, w16

  ret

/**
 * Compute the approximated commitment vector W_approx.
 *
 * This routine computes INTT(A * NTT(Z) - NTT(C) * NTT(T1 * 2^d)) analogously
 * to line 9 in Algorithm 8 of FIPS-204. The signature vector Z shall be passed
 * in decoded form and the public-key vector T1 in encoded form which is
 * undecoded on-the-fly. Similarly, the polynomial matrix A is expanded
 * on-the-fly using the RHO seed. The input values are not preserved.
 *
 * Note that this routine alone accounts for almost 90% of all verify cycles.
 *
 * @param[in] x2: DMEM address of RHO (32 bytes in a 64 byte region).
 * @param[in] x3: DMEM address of Z (7168 bytes).
 * @param[in] x4: DMEM adresss of C (1024 bytes).
 * @param[in] x5: DMEM address of encoded T1 (2560 bytes).
 * @param[in] x6: DMEM address of the result W_approx (8192 bytes).
 * @param[in] x7: DMEM address of a polynomial slot (1024 bytes).
 */
compute_w_approx:
  /* Save DMEM address pointers. */
  addi x8, x2, 0  /* RHO */
  addi x9, x3, 0  /* Z */
  addi x10, x4, 0 /* C */
  addi x11, x5, 0 /* T1_enc */
  addi x12, x6, 0 /* W_approx */
  addi x13, x7, 0 /* Slot */

  /* Make sure the output location is properly zeroized. Dangling non-zero
     values can make the matrix multiplication fail (see `poly_mul_add`). */
  addi x20, x12, 0
  addi x21, x0, 256
  jal x1, zeroize

  /*
   * Part 1: Compute A * NTT(Z), where A is 8x7 polynomial matrix and Z is the
   * signature vector. A is sampled on-the-fly.
   */

  /* Transfer the Z vector into NTT domain in-place. */
  addi x14, x9, 0
  loopi 7, 4
    addi x2, x14, 0
    addi x3, x14, 0
    jal x1, ntt
    addi x14, x14, 1024
    /* End of loop */

  /* Indices r, s for the expansion of A. */
  addi x14, x0, 0
  addi x15, x0, 0

  /* Temp address pointers for Z and W_approx. */
  addi x16, x9, 0
  addi x17, x12, 0

  /* Compute W_approx = A * NTT(Z). */
  loopi 8, 17
    loopi 7, 12
      /* Expand A[r][s] into the slot. */
      addi x2, x13, 0
      addi x3, x8, 0
      addi x4, x14, 0
      addi x5, x15, 0
      jal x1, expand_a

      /* W_approx[r] += A[r][s] * Z[s]. */
      addi x2, x13, 0
      addi x3, x16, 0
      addi x4, x17, 0
      addi x5, x17, 0
      jal x1, poly_mul_add

      /* Increment s and the Z address pointer. */
      addi x15, x15, 1
      addi x16, x16, 1024
      /* End of loop */

  /* Increment r, reset s and the Z address pointer, advance the W_approx
     pointer. */
  addi x14, x14, 1
  addi x15, x0, 0
  addi x16, x9, 0
  addi x17, x17, 1024
  /* End of loop */

  /*
   * Part 2: Compute the subtraction INTT(A * NTT(Z) - NTT(C) * NTT(T1)) by
   * decoding T1 on-the-fly.
   */

  /* Temp W_approx address pointer. */
  addi x14, x12, 0

  /* Map C into NTT domain in-place. */
  addi x2, x10, 0
  addi x3, x10, 0
  jal x1, ntt

  /* Compute W_approx[i] = INTT((A * NTT(Z))[i] - NTT(C) * NTT(T1[i] * 2^d)). */
  loopi 8, 22
    /* Decode T1[i] into slot 0. */
    addi x2, x11, 0
    addi x3, x13, 0
    jal x1, decode_t1

    /* Shift left: T1[i] * 2^d. */
    addi x2, x13, 0
    addi x3, x13, 0
    jal x1, shift_left

    /* Map T1[i] * 2^d into NTT domain in-place. */
    addi x2, x13, 0
    addi x3, x13, 0
    jal x1, ntt

    /* Calculate T1[i] = c * T1[i]. */
    addi x2, x10, 0
    addi x3, x13, 0
    addi x4, x13, 0
    jal x1, poly_mul

    /* Calculate W[i] = W[i] - c * T1[i]. */
    addi x2, x14, 0
    addi x3, x13, 0
    addi x4, x14, 0
    jal x1, poly_sub

    /* Map the result back to the time domain. */
    addi x2, x14, 0
    addi x3, x14, 0
    jal x1, intt

    addi x11, x11, 320
    addi x14, x14, 1024
    /* End of loop */

  ret
