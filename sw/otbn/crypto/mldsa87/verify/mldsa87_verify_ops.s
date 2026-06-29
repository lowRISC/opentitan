/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* High-level operations for the ML-DSA-87 verify function. */

.globl sig_decode
.globl check_infinity_norm_z
.globl compute_w_approx
.globl use_hint
.globl check_hint

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

/**
 * Check that the hint is valid.
 *
 * Given the encoded hint bytes in the intermediate representation generated
 * by `sig_decode`, i.e., 83 + 1 4-byte words, this routine verifies its
 * validity by checking three error conditions as specified in the
 * `HintBitUnpack` function (Algorithm 21) of FIPS-204.
 *
 * @param[in]  x2: DMEM address of the hint in the intermediate representation.
 * @param[out] w0: 2^256-1 if the hint is valid, else 0.
 */
check_hint:

  /*
   * The hint encodes which indices in the K = 8 polynomials in W1_APPROX need
   * to be corrected. The encoding is of the following form:
   *
   * | X00, ..., X0A | X10, ..., X1B | ... | X70, ..., X7H | 0 ... 0 | A + 1, B + 1, ..., H + 1 |
   *    ^               ^                     ^                 ^        ^                  ^
   *    |               |                     |                 |        |                  |
   *   H[0]           H[A+1]                H[G+1]           Padding  H[OMEGA+0]         H[OMEGA+7]
   *
   * Here X0[0-A] denotes the A coefficient indices of the first polynomial
   * that need correction while X7[0-H] denotes the same thing for the H
   * coefficients in the eight polynomial. Bytes 75 to 82 serve as a lookup
   * table that indicates the last element of each of the eight subsequences.
   * For example, Bytes 0 to A correspond to the first polynomial, bytes
   * A + 1 to B to the second polynomial and so on.
   *
   * A correctly encoded hint respects three conditions that need to be
   * verified before it can be unpacked correctly:
   *
   *   1. 0 <= H[OMEGA+0] <= H[OMEGA+1] <= ... <= H[OMEGA+7] <= OMEGA.
   *
   *   2. X00 < X01 < ... X0A, X10 < X11 < ... X1B, etc.
   *
   *   3. H[H+1] to H[OMEGA-1] = 0.
   */

  /*
   * We follow the `HintBitUnpack` function from FIPS-204 in a verbatim manner
   * and early-exit the routine upon encountering the first violation of one
   * of the three conditions.
   *
   * index = 0
   * k = 8
   *
   * for i in [0, k - 1]:
   *
   *   # Condition 1
   *   if H[OMEGA + i] < index or H[OMEGA + i] > OMEGA:
   *     return 0
   *   end if
   *
   *   first = index
   *
   *   while index < H[OMEGA + i]:
   *     # Condition 2
   *     if index > first and H[index - 1] >= H[index]:
   *       return 0
   *     end if
   *
   *     index = index + 1
   *
   *   end while
   *
   * end for
   *
   * for i in [index, OMEGA - 1]:
   *   # Condition 3
   *   if H[i] != 0:
   *     return 0
   *   end if
   *
   * end for
   *
   * return 2^256 - 1
   */

  /* Set up variables and constants. */
  addi x3, x0, 0 /* i */
  addi x4, x0, 0 /* index */

  addi x5, x0, 8  /* k */
  addi x6, x0, 75 /* OMEGA */

  bn.xor w0, w0, w0 /* flag */

  /*
   * Outer for-loop and inner while-loop to check conditions 1 and 2.
   */
_check_hint_outer_loop:

  /* Calculate the address of H[OMEGA + i]. Note that the intermediate
     representation created by `sig_decode` inserts a zero byte at index 75
     which means the first element of the lookup table is actually at
     H[OMEGA + 1 + 0]. For simplicity, we drop the +1 below. */
  add x7, x3, x6
  addi x7, x7, 1
  slli x7, x7, 2
  add x7, x7, x2

  /* Load H[OMEGA + i]. */
  lw x8, 0(x7)

  /* Condition 1. */

  /* H[OMEGA + i] >= index. */
  sub x7, x8, x4
  srai x7, x7, 31
  bne x7, x0, _check_hint_end

  /* H[OMEGA + i] <= OMEGA. */
  sub x7, x6, x8
  srai x7, x7, 31
  bne x7, x0, _check_hint_end

  addi x7, x4, 0 /* first = index. */

  /*
   * Start of the inner while-loop.
   */
_check_hint_inner_loop_start:

  /* Exit the while-loop if index >= H[OMEGA + i]. */
  sub x9, x8, x4
  addi x9, x9, -1
  srai x9, x9, 31
  bne x9, x0, _check_hint_inner_loop_end

  /* If index <= first, then skip the second check. The skip is necessary to
     prevent out-of-bounds memory accesses. */
  sub x9, x4, x7
  addi x9, x9, -1
  srai x9, x9, 31
  bne x9, x0, _check_hint_inner_loop_cond_skip

  /* Calculate the address of H[index]. */
  slli x9, x4, 2
  add x9, x9, x2

  /* Load H[index - 1] and H[index]. */
  lw x10, -4(x9)
  lw x11, 0 (x9)

  /* Condition 2. */

  /* H[index - 1] < H[index]. */
  sub x9, x11, x10
  addi x9, x9, -1
  srai x9, x9, 31
  bne x9, x0, _check_hint_end

_check_hint_inner_loop_cond_skip:

  /* Increment index and jump to the start of the while loop. */
  addi x4, x4, 1
  jal x0, _check_hint_inner_loop_start

_check_hint_inner_loop_end:

  /* Increment i and jump back to the start of the for-loop if i < k. */
  addi x3, x3, 1
  bne x3, x5, _check_hint_outer_loop

  /* At this point conditions 1 and 2 have been successfully verified. */

  addi x3, x4, 0 /* i = index */

  /*
   * Start of the final for-loop.
   */
_check_hint_final_loop_start:

  /* Exit the loop, if i = OMEGA. */
  beq x3, x6, _check_hint_final_loop_end

  /* Calculate the address of H[i]. */
  slli x9, x3, 2
  add x9, x9, x2

  /* Load H[i]. */
  lw x10, 0(x9)

  /* Condition 3. */

  /* H[0] == 0. */
  bne x10, x0, _check_hint_end

  /* Increment i and jump to the start of the final loop. */
  addi x3, x3, 1
  jal x0, _check_hint_final_loop_start

_check_hint_final_loop_end:

  /* Arriving here means the hint has passed the validity check and we can set
     the return flag to 2^256 - 1. */

  bn.not w0, w0

_check_hint_end:
  ret
