/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* High-level operations for the ML-DSA-87 verify function. */

.globl sig_decode
.globl check_infinity_norm_z
.globl compute_w_approx
.globl use_hint

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

/**
 * Returns the hint-adjusted high level bits W1 of the commitment vector W
 * in encoded form (8 * 128 bytes).
 *
 * For the signature verification to succeed, the approximation of the high bits
 * in the commitment vector needs to be corrected using the hint. This routine
 * implements the `UseHint` function (Algorithm 40) of FIPS-204. The
 * coefficients of the output polynomials lie in the interval
 * [0, (q-1)/(2*gamma2)[ = [0, 15].
 *
 * This routine is in-place meaning that the corrected and encoded W1 vector
 * resides at DMEM[x2].
 *
 * The hint vector is assumed to be provided in the intermediate encoded
 * representation (see `sig_decode`).
 *
 * @param[in] x2: DMEM address of the approximated commitment vector W_approx.
 * @param[in] x3: DMEM address of the undecoded hint vector H.
 * @param[in] x4: DMEM address of the polynomial slot 0.
 * @param[in] x5: DMEM address of the polynomial slot 1.
 */
use_hint:

  /*
    The original commitment vector is calculated by HighBits(AZ - CT), however
    due to the decomposition of  T = T1 * 2^d + T0, the verifier can only
    compute AZ - CT + CT0. Since CT0 contains only small-norm coefficients, all
    we need to know to recreate HighBits(AZ - CT) from AZ - CT + CT0 is which
    coefficients of HighBits(AZ - CT) would change with the subtraction of CT0.
    So the hint is basically the carry bits of the subtraction of CT0.
   */

  /* Prepare the address pointers. */
  addi x6, x2, 0 /* w1_approx */
  addi x7, x3, 0 /* h */
  addi x8, x4, 0 /* slot 0 */
  addi x9, x5, 0 /* slot 1 */

  /* Index counter for the decoding of the hint polynomials. */
  addi x10, x0, 0

  /* WDR pointers. */
  addi x11, x0, 0
  addi x12, x0, 1
  addi x13, x0, 2

  /*
   * The adjustment algorithm first decomposes the input polynomial in low (r0)
   * and high (r1) bits polynomials, then decodes the i-th hint polynomial and
   * adjusts each of the 256 coefficients in r1 per inner loop.
   */
  loopi 8, 28
    /* Decompose W[i] and put the high bits in the output location and the low
      bits into slot 0. */
    addi x2, x6, 0
    addi x3, x8, 0 /* r0 */
    addi x4, x6, 0 /* r1 */
    jal x1, decompose

    /* Decode H[i] and place into slot 1. */
    addi x2, x7, 0
    addi x3, x9, 0
    addi x4, x10, 0
    jal x1, decode_h

    /* Prepare constant vectors. Due to clobbered WDRs place them inside the
       loop. */

    /* [1, 1, 1, 1, 1, 1, 1, 1]. */
    bn.not w6, w31
    bn.shv.8s w6, w6 >> 31
    /* [15, 15, 15, 15, 15, 15, 15, 15]. */
    bn.not w7, w31
    bn.shv.8s w7, w7 >> 28

    loopi 32, 12
      bn.lid x11, 0(x8++) /* r0 */
      bn.lid x12, 0(x6)   /* r1 */
      bn.lid x13, 0(x9++) /* h  */

      /* Create a mask for h; -1 if h = 1, else 0. */
      bn.subv.8s w2, w31, w2

      /*
       * Merge lines 3, 4, and 5 of Algorithm 40 into one operation that
       * calculates (r1 + x) mod 16 where
       *   x =  1 if h = 1 and r0 > 0,
       *   x = -1 if h = 1 and r0 <= 0,
       *   x = 0 otherwise.
       */

      /* x = -1 if r0 <= 0, else x = 0. */
      bn.subv.8s w3, w0, w6
      bn.shv.8s w3, w3 >> 31
      bn.subv.8s w3, w31, w3
      /* x = -1 if r0 <= 0, else x = 1. */
      bn.or w3, w3, w6
      /* x = -1 if r0 <= 0 and h = 1; x = 1 if r0 > 0 and h = 1. */
      bn.and w5, w3, w2

      /* r1 + x mod 16. */
      bn.addv.8s w1, w1, w5
      bn.and w1, w1, w7

      bn.sid x12, 0(x6++)
      /* End of loop */

    /* Advance/reset address pointers and hint index. */
    addi x8, x8, -1024
    addi x9, x9, -1024
    addi x10, x10, 1
    /* End of loop */

  /* Restore the w1 pointer and encode w1 in-place.  */
  addi x2, x0, 1024
  slli x2, x2, 3
  sub  x2, x6, x2
  addi x3, x2, 0
  loopi 8, 3
    jal x1, encode_w1
    addi x2, x2, 1024
    addi x3, x3, 128
    /* End of loop */

  ret
