/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* High-level operations for ML-DSA-87 sign. */

.globl compute_w
.globl decompose_w
.globl compute_z
.globl compute_r0

.text

/**
 * Compute the commitment vector W = A * Y.
 *
 * Calculate a matrix-vector multiplication of a 8x7 matrix A and a 7x1 vector
 * Y to produce the commitment vector W (2 * 8192 bytes). The individual
 * polynomials of both A and Y are generated on-the-fly through `expand_a` and
 * `expand_mask` respectively. `expand_a` requires a 34-byte seed RHO (in a
 * 64-byte region) and `expand_mask` requires a Boolean-shared 66-byte seed
 * RHO_PRIME (in a 96-byte region). Furthermore, three polynomial slots are
 * required for the storage of intermediate results.
 *
 * @param[in] x2: DMEM address of first share of the commitment vector W.
 * @param[in] x3: DMEM address of second share of the commitment vector W.
 * @param[in] x4: DMEM address of the matrix seed RHO.
 * @param[in] x5: DMEM address of the first share of the vector seed RHO_PRIME.
 * @param[in] x6: DMEM address of the second share of the vector seed RHO_PRIME.
 * @param[in] x7: DMEM address of polynomial slot 0 (1024 bytes).
 * @param[in] x8: DMEM address of polynomial slot 1 (1024 bytes).
 * @param[in] x9: DMEM address of polynomial slot 2 (1024 bytes).
 */
compute_w:
  /* Prepare DMEM address registers. */
  addi x10, x2, 0 /* W0 (W share 0) */
  addi x11, x3, 0 /* W1 (W share 1) */
  addi x12, x4, 0 /* RHO */
  addi x13, x5, 0 /* RHO_PRIME_0 (RHO_PRIME share 0) */
  addi x14, x6, 0 /* RHO_PRIME_1 (RHO_PRIME share 1) */
  addi x15, x7, 0 /* Slot 0 */
  addi x16, x8, 0 /* Slot 1 */
  addi x17, x9, 0 /* Slot 2 */

  /* Zeroize the output DMEM locations just to be safe. */
  addi x20, x10, 0
  addi x21, x0, 256
  jal x1, zeroize

  addi x20, x11, 0
  addi x21, x0, 256
  jal x1, zeroize

  /* Loop indices for the `expand_a` and `expand_mask`. */
  addi x18, x0, 0 /* r */
  addi x19, x0, 0 /* s */

  /*
   * The matrix-vector multiplication proceeds in column-major order:
   *
   * for s in [0, 6]:
   *   Y0[s], Y1[s] = expand_mask(RHO_PRIME_0, RHO_PRIME_1, s)
   *   Y0[s], Y1[s] = NTT(Y0[s]), NTT(Y1[s])
   *   for r in [0, 7]:
   *     A[r][s] = expand_a(RHO, r, s)
   *     W0[r] += A[r][s] * Y0[s]
   *     W1[r] += A[r][s] * Y1[s]
   *   end for
   * end for
   */
  loopi 7, 37
    /* Expand polynomials Y0[s] and Y1[s] and store them in slots 1 and 2. */
    addi x2, x16, 0
    addi x3, x17, 0
    addi x4, x13, 0
    addi x5, x14, 0
    addi x6, x19, 0
    jal x1, expand_mask

    /* Compute NTT(Y0[s]). */
    addi x2, x16, 0
    addi x3, x16, 0
    jal x1, ntt

    /* Compute NTT(Y1[s]). */
    addi x2, x17, 0
    addi x3, x17, 0
    jal x1, ntt

    loopi 8, 18
      /* Expand polynomial A[r][s] and store it at slot 0. */
      addi x2, x15, 0
      addi x3, x12, 0
      addi x4, x18, 0
      addi x5, x19, 0
      jal x1, expand_a

      /* W0[r] += A[r][s] * NTT(Y0[s]). */
      addi x2, x15, 0
      addi x3, x16, 0
      addi x4, x10, 0
      addi x5, x10, 0
      jal x1, poly_mul_add

      /* W1[r] += A[r][s] * NTT(Y1[s]). */
      addi x2, x15, 0
      addi x3, x17, 0
      addi x4, x11, 0
      addi x5, x11, 0
      jal x1, poly_mul_add

      /* Increment r and advance output addresses. */
      addi x18, x18, 1
      addi x10, x10, 1024
      addi x11, x11, 1024
      /* End of loop */

    /* Reset r and increment s. */
    addi x18, x0, 0
    addi x19, x19, 1

    /* Reset the output addresses, i.e., subtract 8192. */
    addi x20, x0, 1024
    slli x20, x20, 3
    sub x10, x10, x20
    sub x11, x11, x20
    /* End of loop */

  /* Map the result polynomials back to the time domain. */
  loopi 8, 8
    /* W0[r] = INTT(W0[r]). */
    addi x2, x10, 0
    addi x3, x10, 0
    jal x1, intt

    /* W1[r] = INTT(W1[r]). */
    addi x2, x11, 0
    addi x3, x11, 0
    jal x1, intt

    addi x10, x10, 1024
    addi x11, x11, 1024
    /* End of loop */

  ret

/**
 * Decomposition of the commitment vector W.
 *
 * Decompose the shared commitment vector W = A * Y into lower-bit polynomials
 * W0 and higher-bit polynomials W1 according to the `Decompose` function
 * (Algorithm 36) of FIPS-204. See `sec_decompose` for the mathematical
 * rationale behind this operation.
 *
 * This routine overwrites the DMEM location of W with the W0 polynomials and
 * encodes the W1 polynomials to a dense representation (see `encode_w1`).
 *
 * @param[in] x2: DMEM address of the first share of W and the first share of
 *                the resulting W0 (both 8 * 1024 bytes).
 * @param[in] x3: DMEM address of the second share of W and the second share of
 *                the resulting W0 (both 8 * 1024 bytes).
 * @param[in] x4: DMEM address of the encoded W1 vector (8 * 128 bytes).
 * @param[in] x5: DMEM address of a polynomial slot (1024 bytes).
 */
decompose_w:
  /* Save DMEM address pointers. */
  addi x6, x2, 0 /* W (share 0) */
  addi x7, x3, 0 /* W (share 1) */
  addi x8, x4, 0 /* W1 */
  addi x9, x5, 0 /* Slot */

  /*
   * Iterate over each shared polynomial W[i] and decompose it into a shared
   * polynomial whose coefficients contain the lower bits W0[i] and an unshared
   * polynomial for the high-bit coefficients W1[i]. To save DMEM space, W1[i]
   * is immediately encoded into a dense representation.
   */
  loopi 8, 10
    /* Compute the decomposition of W[i]. Overwrite the two shares of W[i] with
       the shares of W0[i] and place W1[i] in the slot. */
    addi x2, x6, 0
    addi x3, x7, 0
    addi x4, x9, 0
    jal x1, sec_decompose

    /* Encode W1[i] in the slot and write it to the output location. */
    addi x2, x9, 0
    addi x3, x8, 0
    jal x1, encode_w1

    /* Advance address pointers. */
    addi x6, x6, 1024
    addi x7, x7, 1024
    addi x8, x8, 128
    /* End of loop */

  ret

/**
 * Compute the signature vector Z and check its infinity norm.
 *
 * This routine calculates Z = Y + INTT(NTT(C) * NTT(S1)) with arithmetically
 * shared vectors Y and S1 which are expanded, decoded and converted to
 * arithmetic shares on on-the-fly (see `expand_mask` and `decode_s`). The
 * `expand_mask` seed RHO_PRIME is assumed to be passed as 66-bytes in a
 * 96-byte region as two Boolean shares. The S1 vector is assumed to be passed
 * in encoded form, i.e., as two 672-byte Boolean shares.
 *
 * Each derived signature polynomial Z[i] undergoes a secure infinity norm
 * check |Z[i]|_inf < 2^19 - BETA before being unmasked.
 *
 * @param[in] x2:  DMEM address of the first share of RHO_PRIME seed.
 * @param[in] x3:  DMEM address of the second share of RHO_PRIME seed.
 * @param[in] x4:  DMEM address of the challenge polynomial C in NTT domain.
 * @param[in] x5:  DMEM address of the first share of the encoded vector S1.
 * @param[in] x6:  DMEM address of the second share of the encoded vector S1.
 * @param[in] x7:  DMEM address of the vectorized bound 2^19 - BETA (32 bytes).
 * @param[in] x8:  DMEM address of the resulting signature vector Z.
 * @param[in] x9:  DMEM address of the polynomial slot 0.
 * @param[in] x10: DMEM address of the polynomial slot 1.
 * @param[in] x11: DMEM address of the polynomial slot 2.
 * @param[in] x12: DMEM address of the polynomial slot 3.
 * @param[out] w0: 2^256-1 if the norm check passes, 0 otherwise.
 */
compute_z:
  /* Save DMEM address pointers. */
  addi x13, x2, 0 /* RHO_PRIME_0 (RHO_PRIME share 0) */
  addi x14, x3, 0 /* RHO_PRIME_1 (RHO_PRIME share 1) */
  addi x15, x4, 0 /* NTT(C) */
  addi x16, x5, 0 /* S1_0_enc (encoded S1 share 0) */
  addi x17, x6, 0 /* S1_1_enc (encoded S1 share 1) */

  /*
   * Do not save those address pointers which are not overwritten:
   *   x7:  Bound
   *   x8:  Z
   *   x9:  Slot 0
   *   x10: Slot 1
   *   x11: Slot 2
   *   x12: Slot 3
   */

  /* Loop index for `expand_mask`. */
  addi x18, x0, 0 /* s */

  /*
   * Calculate and norm-check the individual polynomials of the signature
   * vector Z as follows. Importantly, we cannot unmask the polynomials until
   * the norm check has passed for one of them. This means, due to the DMEM
   * constraints, we need to calculate the masked Z polynomials effectively
   * twice, once for the bound check and then to unmask them.
   *
   * def kernel:
   *   Y0[s], Y1[s] = expand_mask(RHO_PRIME_0, RHO_PRIME_1, s)
   *   S1_0[s], S1_1[s] = decode_s(S1_0_enc[s], S1_1_enc[s])
   *
   *   A0, A1 = NTT(S1_0[s]), NTT(S1_1[s])
   *   B0, B1 = NTT(C) * A0, NTT(C) * A1
   *   C0, C1 = INTT(B0), INTT(B1)
   *   D0, D1 = Y0[s] + C0, Y1[s] + C1
   *   return D0, D1
   * enddef
   *
   * # Loop 1: norm check.
   *
   * for s in [0, 6]:
   *   D0, D1 = kernel()
   *
   *   if |D0, D1|_inf >= bound:
   *     return 0
   *   endif
   * endfor
   *
   * # Loop 2: computation of Z.
   *
   * for s in [0, 6]:
   *   D0, D1 = kernel()
   *   Z[s] = D0 + D1 (unmasking)
   * endfor
   *
   * return 2^256 - 1
   */

  /*
   * Part 1: Norm check the Z[s] polynomials.
   */

  /* XXX: Check whether early abort is fine with regards to hardening. */
_compute_z_norm_check_loop:
  /* Compute the arithmetic shares of Z[s]. */
  jal x1, _compute_z_kernel

  /* Compute the infinity norm check on the shared signature polynomial and
     exit the routine if it fails. */
  addi x2, x9, 0
  addi x3, x10, 0
  addi x4, x7, 0
  jal x1, sec_bound_check

  /* Fail if w0 = 0. */
  bn.cmp w0, w31, FG0
  csrrs x2, FG0, x0
  andi x2, x2, 0x8
  bne x2, x0, _compute_z_fail

  /* Increment s, advance S1 pointers. */
  addi x18, x18, 1
  addi x16, x16, 96
  addi x17, x17, 96

  /* Loop until all the Z[s] have been norm-checked. */
  addi x2, x0, 7
  bne x18, x2, _compute_z_norm_check_loop

  /*
   * Part 2: Compute all the Z[s] polynomials.
   */

  /* Reset the loop index s and the S1 pointers. */
  addi x18, x0, 0
  addi x16, x16, -672
  addi x17, x17, -672

  loopi 7, 9
    /* Compute the arithmetic shares of Z[s]. */
    jal x1, _compute_z_kernel

    /* At this point, due to the passed infinity norm check, Z0 and Z1 are not
       considered sensitive anymore and can be unmasked (see Section 3.2 in [1]).
         Z[s] = D0 + D1 (unmasking). */
    addi x2, x9, 0
    addi x3, x10, 0
    addi x4, x8, 0
    jal x1, sec_unmask

    /* Increment s, advance S1 and Z pointers. */
    addi x18, x18, 1
    addi x16, x16, 96
    addi x17, x17, 96
    addi x8, x8, 1024
    /* End of loop */

  /* At this point, all the signature polynomials have been computed and have
     passed the infinity norm check. */
  bn.not w0, w31
  ret

/*
 * Compute the arithmetic shares of Z[s] (see above pseudocode).
 */
_compute_z_kernel:
  /* Expand Y0[s] and Y1[s] as arithmetic shares into slots 0 and 1. */
  addi x2, x9, 0
  addi x3, x10, 0
  addi x4, x13, 0
  addi x5, x14, 0
  addi x6, x18, 0
  jal x1, expand_mask

  /* Decode S1_0_enc[s] and S1_1_enc[s] as arithmetic shares into slots 2 and 3. */
  addi x2, x16, 0
  addi x3, x17, 0
  addi x4, x11, 0
  addi x5, x12, 0
  jal x1, decode_s

  /* A0 = NTT(S1_0[s]). */
  addi x2, x11, 0
  addi x3, x11, 0
  jal x1, ntt

  /* A1 = NTT(S1_1[s]). */
  addi x2, x12, 0
  addi x3, x12, 0
  jal x1, ntt

  /* B0 = NTT(C) * A0 = NTT(C) * S1_0[s]. */
  addi x2, x15, 0
  addi x3, x11, 0
  addi x4, x11, 0
  jal x1, poly_mul

  /* B1 = NTT(C) * A1 = NTT(C) * S1_1[s]. */
  addi x2, x15, 0
  addi x3, x12, 0
  addi x4, x12, 0
  jal x1, poly_mul

  /* C0 = INTT(B0) = INTT(NTT(C) * S1_0[s]). */
  addi x2, x11, 0
  addi x3, x11, 0
  jal x1, intt

  /* C1 = INTT(B1) = INTT(NTT(C) * S1_1[s]). */
  addi x2, x12, 0
  addi x3, x12, 0
  jal x1, intt

  /* D0 = Y0[s] + C0 = Y0[s] + INTT(NTT(C) * S1_0[s]). */
  addi x2, x9, 0
  addi x3, x11, 0
  addi x4, x9, 0
  jal x1, poly_add

  /* D1 = Y1[s] + C1 = Y1[s] + INTT(NTT(C) * S1_1[s]). */
  addi x2, x10, 0
  addi x3, x12, 0
  addi x4, x10, 0
  jal x1, poly_add

  ret

  /* Failure case, a signature polynomial has failed the infinity norm check. */
_compute_z_fail:
  bn.xor w0, w0, w0

  ret

/**
 * Compute the R0 vector and check its infinity norm.
 *
 * This routine computes R0 = W0 - INTT(NTT(C) * NTT(S2)) with arithmetically
 * shared vectors W0 and S2 with S2 being decoded and converted to arithmetic
 * shares on-the-fly (see `decode_s`). The S2 vector is assumed to be passed in
 * encoded form, i.e., as two 768-byte Boolean shares. This routine overwrites
 * the DMEM locations of the shared W0 polynomials.
 *
 * The computation deviates slightly from FIPS-204 as it directly operates on
 * the lower-bit polynomials W0 of the commitment vector W. This choice makes
 * it possible to completely unmask R0 after it has passed the bound check. For
 * more details on this implementation choice see Section 3.2 in Azouaoui et
 * al.'s paper "Protecting Dilithium against Leakage":
 * https://tches.iacr.org/index.php/TCHES/article/view/11158/10597.
 *
 * Each derived polynomial R0[i] undergoes a secure infinity norm check
 * |R0[i]|_inf < GAMMA2 - BETA before being unmasked.
 *
 * @param[in] x2:  DMEM address of the first share of W0 and the resulting R0.
 * @param[in] x3:  DMEM address of the second share of W0.
 * @param[in] x4:  DMEM address of the challenge polynomial C in NTT domain.
 * @param[in] x5:  DMEM address of the first share of the encoded vector S2.
 * @param[in] x6:  DMEM address of the second share of the encoded vector S2.
 * @param[in] x7:  DMEM address of the vectorized bound GAMMA2 - BETA (32 bytes).
 * @param[in] x8:  DMEM address of the polynomial slot 0.
 * @param[in] x9:  DMEM address of the polynomial slot 1.
 * @param[out] w0: 2^256-1 if the norm check passes, 0 otherwise.
 */
compute_r0:
  /* Save DMEM address pointers. */
  addi x10, x2, 0 /* W0_0 (W0 share 0) */
  addi x11, x3, 0 /* W0_1 (W0 share 1) */
  addi x12, x4, 0 /* NTT(C) */
  addi x13, x5, 0 /* S2_0_enc (encoded S2 share 0) */
  addi x14, x6, 0 /* S2_1_enc (encoded S2 share 1) */

  /*
   * Do not save those address pointers which are not overwritten:
   *   x7: Bound
   *   x8: Slot 0
   *   x9: Slot 1
   */

  /* Loop index. */
  addi x15, x0, 0 /* r */

  /*
   * Calculate the individual polynomials of the vector R0 as follows:
   *
   * for r in [0, 7]:
   *   S2_0[r], S2_1[r] = decode_s(S2_0_enc[r], S2_1_enc[r])
   *
   *   A0, A1 = NTT(S2_0[s]), NTT(S2_1[s])
   *   B0, B1 = NTT(C) * A0, NTT(C) * A1
   *   C0, C1 = INTT(B0), INTT(B1)
   *   D0, D1 = W0_0[r] - C0, W0_1[r] - C1
   *
   *   if |D0, D1|_inf >= bound:
   *     return 0
   *   endif
   * endfor
   *
   * for r in [0, 7]:
   *   R0[r] = D0 + D1 (unmasking)
   * endfor
   *
   * return 2^256 - 1
   */
_compute_r0_loop:
  /* Decode S2_0_enc[r] and S2_1_enc[r] as arithmetic shares into slots 0 and 1. */
  addi x2, x13, 0
  addi x3, x14, 0
  addi x4, x8, 0
  addi x5, x9, 0
  jal x1, decode_s

  /* A0 = NTT(S2_0[r]). */
  addi x2, x8, 0
  addi x3, x8, 0
  jal x1, ntt

  /* A1 = NTT(S2_1[r]). */
  addi x2, x9, 0
  addi x3, x9, 0
  jal x1, ntt

  /* B0 = NTT(C) * A0 = NTT(C) * S2_0[r]. */
  addi x2, x12, 0
  addi x3, x8, 0
  addi x4, x8, 0
  jal x1, poly_mul

  /* B1 = NTT(C) * A1 = NTT(C) * S2_1[r]. */
  addi x2, x12, 0
  addi x3, x9, 0
  addi x4, x9, 0
  jal x1, poly_mul

  /* C0 = INTT(B0) = INTT(NTT(C) * S2_0[r]). */
  addi x2, x8, 0
  addi x3, x8, 0
  jal x1, intt

  /* C1 = INTT(B1) = INTT(NTT(C) * S2_1[r]). */
  addi x2, x9, 0
  addi x3, x9, 0
  jal x1, intt

  /* D0 = W0_0[r] - C0 = W0_0[r] - INTT(NTT(C) * S2_0[r]). */
  addi x2, x10, 0
  addi x3, x8, 0
  addi x4, x10, 0
  jal x1, poly_sub

  /* D1 = W0_1[r] - C1 = W0_1[r] - INTT(NTT(C) * S2_1[r]). */
  addi x2, x11, 0
  addi x3, x9, 0
  addi x4, x11, 0
  jal x1, poly_sub

 /* Compute the infinity norm check on the shared R0[r] polynomial and exit
    the routine if it fails. */
  addi x2, x10, 0
  addi x3, x11, 0
  addi x4, x7, 0
  jal x1, sec_bound_check

  /* Fail if w0 = 0. */
  bn.cmp w0, w31, FG0
  csrrs x2, FG0, x0
  andi x2, x2, 0x8
  bne x2, x0, _compute_r0_fail

  /* Increment r, advance W0 and S2 pointers. */
  addi x10, x10, 1024
  addi x11, x11, 1024
  addi x13, x13, 96
  addi x14, x14, 96
  addi x15, x15, 1

  /* Loop until all the R0[r] have been computed. */
  addi x2, x0, 8
  bne x15, x2, _compute_r0_loop

  /* Reset the R0[s] address pointers. */
  li x2, 8192
  sub x10, x10, x2
  sub x11, x11, x2

  /* At this point, due to the passed infinity norm check, D0 and D1 are not
     considered sensitive anymore and can be unmasked (see Section 3.2 in [1]).
       R0[s] = D0 + D1 (unmasking). */
  loopi 8, 6
    addi x2, x10, 0
    addi x3, x11, 0
    addi x4, x10, 0
    jal x1, sec_unmask

    addi x10, x10, 1024
    addi x11, x11, 1024
    /* End of loop */

  /* At this point, all the R0 polynomials have been computed and have passed
     the infinity norm check. */
  bn.not w0, w31
  ret

  /* Failure case, a R0 polynomial has failed the infinity norm check. */
_compute_r0_fail:
  bn.xor w0, w0, w0

  ret
