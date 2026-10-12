/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.include "mldsa87.inc"

/* High-level (vector) operations for ML-DSA-87 keygen, sign and verify. */

/* Keygen */
.globl sample_s
.globl compute_t
.globl encode_t
.globl hash_seed
.globl hash_pk

/* Sign */
.globl compute_rho_prime
.globl compute_w
.globl decompose_w
.globl compute_z
.globl compute_r0
.globl compute_x0
.globl make_hint
.globl hw_check_hint
.globl compress_hint

/* Verify */
.globl sig_decode
.globl check_infinity_norm_z
.globl compute_w_approx
.globl use_hint
.globl check_hint
.globl check_hw_c

/* High-level operations for the ML-DSA key generation function. */

.text

/**
 * Sample the S{1,2} vectors.
 *
 * Given a Boolean-shared 66-byte (in a 96-byte region) seed RHO_PRIME, this
 * routine expands the S1 and S2 polynomials (see `expand_s1` and `expand_s2`)
 * and directly encodes them into the output location. The result are
 * Boolean-shared encoded vectors S1 and S2 (2 * 672 byte, 2 * 768 bytes).
 *
 * Two polynomial slots are required for the storage of intermediate results.
 *
 * @param[in] x2: DMEM address of the first Boolean share RHO_PRIME.
 * @param[in] x3: DMEM address of the second Boolean share RHO_PRIME.
 * @param[in] x4: DMEM address of the first Boolean share of the encoded S1.
 * @param[in] x5: DMEM address of the second Boolean share of the encoded S1.
 * @param[in] x6: DMEM address of the first Boolean share of the encoded S2.
 * @param[in] x7: DMEM address of the second Boolean share of the encoded S2.
 * @param[in] x8: DMEM address of polynomial slot 0 (1024 bytes).
 * @param[in] x9: DMEM address of polynomial slot 1 (1024 bytes).
 */
sample_s:
  /* Prepare DMEM address registers. */
  addi x10, x2, 0 /* RHO_PRIME (share 0) */
  addi x11, x3, 0 /* RHO_PRIME (share 1) */
  addi x12, x4, 0 /* S1_enc (share 0) */
  addi x13, x5, 0 /* S1_enc (share 1) */
  addi x14, x6, 0 /* S2_enc (share 0) */
  addi x15, x7, 0 /* S2_enc (share 1) */

  addi x16, x0, 0 /* s */

  /* Expand the S1 polynomials and encode them. */
  loopi 7, 14    /* SCA_TEST_REPLACE: loopi 1, 14 */
    /* Expand S1[s] into slots 0 and 1. */
    addi x2, x10, 0
    addi x3, x11, 0
    addi x4, x8, 0
    addi x5, x9, 0
    addi x6, x16, 0
    jal x1, expand_s1

    /* Encode S1[s] into the output location. */
    addi x2, x8, 0
    addi x3, x9, 0
    addi x4, x12, 0
    addi x5, x13, 0
    jal x1, encode_s

    /* Advance output pointers and increment s. */
    addi x12, x12, 96
    addi x13, x13, 96
    addi x16, x16, 1
    /* End of loop */

  addi x16, x0, 0 /* r */

  /* Expand the S2 polynomials and encode them. */
  loopi 8, 14    /* SCA_TEST_REPLACE: loopi 1, 14 */
    /* Expand S2[r] into slots 0 and 1. */
    addi x2, x10, 0
    addi x3, x11, 0
    addi x4, x8, 0
    addi x5, x9, 0
    addi x6, x16, 0
    jal x1, expand_s2

    /* Encode S2[r] into the output location. */
    addi x2, x8, 0
    addi x3, x9, 0
    addi x4, x14, 0
    addi x5, x15, 0
    jal x1, encode_s

    /* Advance output pointers and increment r. */
    addi x14, x14, 96
    addi x15, x15, 96
    addi x16, x16, 1
    /* End of loop */

  ret

/**
 * Compute the T vector.
 *
 * This routine computes T = INTT(A * NTT(S1)) + S2 which is a 8x7
 * matrix-vector multiplication followed by vector addition. The individual
 * polynomials of A, S1 and S2 are generated and decoded on-the-fly through
 * `expand_a` and `decode_s` respectively. `expand_a` requires a 34-byte seed
 * RHO (in a 64-byte region).
 *
 * The secret vectors S1 and S2 are assumed to be provided Boolean shares in
 * encoded form (2 * 672 bytes, 2 * 768 bytes). The resulting vector is T
 * is returned in two arithmetic shares (2 * 8192 bytes).
 *
 * Three polynomial slots are required for the storage of intermediate results.
 *
 * @param[in] x2:  DMEM address of the seed RHO.
 * @param[in] x3:  DMEM address of the first Boolean share of the encoded S1.
 * @param[in] x4:  DMEM address of the second Boolean share of the encoded S1.
 * @param[in] x5:  DMEM address of the first Boolean share of the encoded S2.
 * @param[in] x6:  DMEM address of the second Boolean share of the encoded S2.
 * @param[in] x7:  DMEM address of the first arithmetic share of T.
 * @param[in] x8:  DMEM address of the first arithmetic share of T.
 * @param[in] x9:  DMEM address of polynomial slot 0 (1024 bytes).
 * @param[in] x10: DMEM address of polynomial slot 1 (1024 bytes).
 * @param[in] x11: DMEM address of polynomial slot 2 (1024 bytes).
 */
compute_t:
  /* Prepare DMEM address registers. */
  addi x12, x2, 0 /* RHO */
  addi x13, x3, 0 /* S1_0_enc (share 0) */
  addi x14, x4, 0 /* S1_1_enc (share 1) */
  addi x15, x5, 0 /* S2_0_enc (share 0) */
  addi x16, x6, 0 /* S2_1_enc (share 1) */

  /* Loop indices for `expand_a`. */
  addi x17, x0, 0 /* r */
  addi x18, x0, 0 /* s */

  /* Zeroize the vector slots. */
  addi x20, x7, 0
  addi x21, x0, 256
  jal x1, zeroize

  addi x20, x8, 0
  addi x21, x0, 256
  jal x1, zeroize

  /*
   * The matrix-vector multiplication proceeds in column-major order:
   *
   * for s in [0, 6]:
   *   S1_0, S1_1 = decode_s(S1_0_enc[s], S1_1_enc[s])
   *   X0, X1 = NTT(S1_0), NTT(S1_1)
   *   for r in [0, 7]:
   *     A = expand_a(RHO, r, s)
   *     T_0[r] += A * X0
   *     T_1[r] += A * X1
   *   end for
   * end for
   */

  loopi 7, 38    /* SCA_TEST_REPLACE: loopi 1, 38 */
    /* X0, X1 = decode_s(S1_0_enc[s], S1_1_enc[s]) (poly slots 0, 1). */
    addi x2, x13, 0
    addi x3, x14, 0
    addi x4, x9, 0
    addi x5, x10, 0
    jal x1, decode_s

    /* X0 = NTT(S1_0). */
    addi x2, x9, 0
    addi x3, x9, 0
    jal x1, ntt

    /* X1 = NTT(S1_1). */
    addi x2, x10, 0
    addi x3, x10, 0
    jal x1, ntt

    loopi 8, 18    /* SCA_TEST_REPLACE: loopi 1, 18 */
      /* A = expand_a(RHO, r, s) (poly slot 2). */
      addi x2, x11, 0
      addi x3, x12, 0
      addi x4, x17, 0
      addi x5, x18, 0
      jal x1, expand_a

      /* T_0[r] += A * X0 = A * NTT(S1_0). */
      addi x2, x11, 0
      addi x3, x9, 0
      addi x4, x7, 0
      addi x5, x7, 0
      jal x1, poly_mul_add

      /* T_1[r] += A * X1 = A * NTT(S1_1). */
      addi x2, x11, 0
      addi x3, x10, 0
      addi x4, x8, 0
      addi x5, x8, 0
      jal x1, poly_mul_add

      /* Increment r and advance output addresses. */
      addi x7, x7, 1024
      addi x8, x8, 1024
      addi x17, x17, 1
      /* End of loop */

    /* Reset r and increment s. */
    addi x17, x0, 0
    addi x18, x18, 1

    /* Reset the output addresses, i.e., subtract 8192. */
    addi x20, x0, 1024
    slli x20, x20, 3    /* SCA_TEST_REPLACE: slli x20, x20, 0 */
    sub x7, x7, x20
    sub x8, x8, x20

    /* Advance S1_0_enc and S1_1_enc pointers. */
    addi x13, x13, 96
    addi x14, x14, 96
    /* End of loop */

  /*
   * Vector-vector addition:
   *
   * for r in [0, 7]:
   *   T_0[r] = INTT(T_0[r])
   *   T_1[r] = INTT(T_1[r])
   *   X0, X1 = decode_s(S2_0_enc[r], S2_1_enc[r])
   *   T_0[r] += X0
   *   T_1[r] += X1
   * end for
  */

  loopi 8, 23    /* SCA_TEST_REPLACE: loopi 1, 23 */
    /* T_0[r] = INTT(T_0[r]). */
    addi x2, x7, 0
    addi x3, x7, 0
    jal x1, intt

    /* T_1[r] = INTT(T_1[r]). */
    addi x2, x8, 0
    addi x3, x8, 0
    jal x1, intt

    /* X0, X1 = decode_s(S2_0_enc[r], S2_1_enc[r]) (poly slots 0, 1). */
    addi x2, x15, 0
    addi x3, x16, 0
    addi x4, x9, 0
    addi x5, x10, 0
    jal x1, decode_s

    /* T_0[r] += X0. */
    addi x2, x7, 0
    addi x3, x9, 0
    addi x4, x7, 0
    jal x1, poly_add

    /* T_1[r] += X1. */
    addi x2, x8, 0
    addi x3, x10, 0
    addi x4, x8, 0
    jal x1, poly_add

    /* Advance output and S2_enc pointers. */
    addi x7, x7, 1024
    addi x8, x8, 1024
    addi x15, x15, 96
    addi x16, x16, 96
    /* End of loop */

  ret

/**
 * Round and encode T.
 *
 * This routine unmasks the arithmetically shared vector T, rounds it to T0 and
 * T1 vectors which are then encoded on-the-fly.
 *
 * Two polynomial slots are required for the storage of intermediate results.
 *
 * @param[in] x2: DMEM address of the first arithmetic share of T (8192 bytes).
 * @param[in] x3: DMEM address of the second arithmetic share of T (8192 bytes).
 * @param[in] x4: DMEM address of the encoded T0 vector (3328 bytes).
 * @param[in] x5: DMEM address of the encoded T1 vector (2560 bytes).
 * @param[in] x6: DMEM address of polynomial slot 0 (1024 bytes).
 * @param[in] x7: DMEM address of polynomial slot 1 (1024 bytes).
 */
encode_t:
  /* Prepare DMEM address registers. */
  addi x8, x2, 0  /* T (share 0) */
  addi x9, x3, 0  /* T (share 1) */
  addi x10, x4, 0 /* T0_enc */
  addi x11, x5, 0 /* T1_enc */

  /* Unmask, round and encode each T polynomial. */
  loopi 8, 18    /* SCA_TEST_REPLACE: loopi 1, 18 */
    /* Securely unmask T into slot 0. */
    addi x2, x8, 0
    addi x3, x9, 0
    addi x4, x6, 0
    jal x1, sec_unmask

    /* Split T into T0 and T1 in slots 0 and 1. */
    addi x2, x6, 0
    addi x3, x6, 0
    addi x4, x7, 0
    jal x1, power2round

    /* Encode T0 into the output location. */
    addi x2, x6, 0
    addi x3, x10, 0
    jal x1, encode_t0

    /* Encode T1 into the output location. */
    addi x2, x7, 0
    addi x3, x11, 0
    jal x1, encode_t1

    /* Advance T and output pointers.*/
    addi x8, x8, 1024
    addi x9, x9, 1024
    addi x10, x10, 416
    addi x11, x11, 320
    /* End of loop */

  ret

/**
 * Hash the seed Xi.
 *
 * ML-DSA keygen is parametrized by a 32-byte seed Xi (passed as a 34-byte
 * value) that is hashed to create RHO, RHO_PRIME and K, i.e.,
 *
 *   RHO, RHO_PRIME, K = Shake256(Xi),
 *
 * where RHO is a 32-byte unshared value, RHO_PRIME is a 64-byte Boolean-shared
 * value and K is a 32-byte Boolean-shared value.
 *
 * Xi is assumed to be passed as a 34-byte value in a 64-byte region with bytes
 * 32 and 33 of both shares set to 0.
 *
 * @param[in] x2: DMEM address of the first Boolean share of Xi.
 * @param[in] x3: DMEM address of the second Boolean share of Xi.
 * @param[in] x4: DMEM address of RHO.
 * @param[in] x5: DMEM address of the first Boolean share of RHO_PRIME.
 * @param[in] x6: DMEM address of the second Boolean share of RHO_PRIME.
 * @param[in] x7: DMEM address of the first Boolean share of K.
 * @param[in] x8: DMEM address of the second Boolean share of K.
 */
hash_seed:
  /* Squeeze buffer WDR pointers. */
  addi x9, x0, 29
  addi x10, x0, 30

  jal x1, xof_shake256_init

  /* Absorb the 34-byte Boolean shared seed value Xi. */
  addi x20, x0, 34
  addi x21, x2, 0
  addi x22, x3, 0
  jal x1, xof_absorb
  jal x1, xof_process

  /* Squeeze the 32-byte unshared value RHO. */
  jal x1, xof_squeeze32
  bn.xor w29, w29, w30 /* unmask */
  bn.sid x9, 0(x4)

  /* Squeeze the 64-byte Boolean-shared value RHO_PRIME. */
  jal x1, xof_squeeze32
  bn.sid x9, 0(x5)
  bn.xor w31, w31, w31 /* dummy */
  bn.sid x10, 0(x6)
  jal x1, xof_squeeze32
  bn.sid x9, 32(x5)
  bn.xor w31, w31, w31 /* dummy */
  bn.sid x10, 32(x6)

  /* Squeeze the 32-byte Boolean-shared value K. */
  jal x1, xof_squeeze32
  bn.sid x9, 0(x7)
  bn.xor w31, w31, w31 /* dummy */
  bn.sid x10, 0(x8)

  jal x1, xof_finish

  ret

/**
 * Hash the public key.
 *
 * The hash of the 2592-byte public key is 64-byte unshared value TR.
 *
 *   TR = Shake256(PK)
 *
 * @param[in] x2: DMEM address of the 2592-byte public key.
 * @param[in] x3: DMEM address of TR.
 */
hash_pk:
  jal x1, xof_shake256_init

  /* Absorb the entire public key of size 2592 bytes. */
  li x20, 2592
  addi x21, x2, 0
  addi x22, x0, 0
  jal x1, xof_absorb
  jal x1, xof_process

  /* Squeeze the 64-byte value TR. */
  jal x1, xof_squeeze32
  bn.xor w0, w29, w30 /* unmask */
  bn.sid x0, 0(x3)
  jal x1, xof_squeeze32
  bn.xor w0, w29, w30 /* unmask */
  bn.sid x0, 32(x3)

  jal x1, xof_finish

  ret

/* High-level operations for ML-DSA-87 sign. */

.text

/**
 * Compute the Boolean-shared mask seed RHO_PRIME = H(K || RND || MU).
 *
 * @param[in] x2: DMEM address of the first Boolean share of K.
 * @param[in] x3: DMEM address of the second Boolean share of K.
 * @param[in] x4: DMEM address of the first Boolean share of RND.
 * @param[in] x5: DMEM address of the second Boolean share of RND.
 * @param[in] x6: DMEM address of MU.
 * @param[in] x7: DMEM address of the first Boolean share of RHO_PRIME.
 * @param[in] x8: DMEM address of the second Boolean share of RHO_PRIME.
 */
compute_rho_prime:
  jal x1, xof_shake256_init

  /* Absorb both shares of K. */
  addi x20, x0, 32
  addi x21, x2, 0
  addi x22, x3, 0
  jal x1, xof_absorb

  /* Absorb RND. */
  addi x20, x0, 32
  addi x21, x4, 0
  addi x22, x5, 0
  jal x1, xof_absorb

  /* Absorb MU. */
  addi x20, x0, 64
  addi x21, x6, 0
  addi x22, x0, 0
  jal x1, xof_absorb

  jal x1, xof_process

  /* Squeeze both shares of RHO_PRIME. */
  addi x9, x0, 29
  addi x10, x0, 30

  loopi 2, 4
    jal x1, xof_squeeze32

    bn.sid x9, 0(x7++)
    bn.xor w31, w31, w31 /* dummy */
    bn.sid x10, 0(x8++)
    /* End of loop */

  jal x1, xof_finish

  ret

/**
 * Compute the commitment vector W = A * Y.
 *
 * Calculate a matrix-vector multiplication of a 8x7 matrix A and a 7x1 vector
 * Y to produce the commitment vector W (2 * 8192 bytes). The individual
 * polynomials of both A and Y are generated on-the-fly through `expand_a` and
 * `expand_mask` respectively. `expand_a` requires a 34-byte seed RHO (in a
 * 64-byte region) and `expand_mask` requires a Boolean-shared 64-byte seed
 * RHO_PRIME and 2-byte nonce KAPPA (in a 32-byte DMEM region). Furthermore,
 * three polynomial slots are required for the storage of intermediate results.
 *
 * @param[in] x2: DMEM address of first share of the commitment vector W.
 * @param[in] x3: DMEM address of second share of the commitment vector W.
 * @param[in] x4: DMEM address of the matrix seed RHO.
 * @param[in] x5: DMEM address of the first share of the vector seed RHO_PRIME.
 * @param[in] x6: DMEM address of the second share of the vector seed RHO_PRIME.
 * @param[in] x7: DMEM address of KAPPA.
 * @param[in] x8: DMEM address of the polynomial slots (slots 0-2 are used).
 */
compute_w:
  /* Save address of slot 2 for easier access later. */
  addi x9, x8, 2047
  addi x9, x9, 1

  /* Prepare DMEM address registers. */
  addi x10, x2, 0 /* W0 (W share 0) */
  addi x11, x3, 0 /* W1 (W share 1) */
  addi x12, x4, 0 /* RHO */
  addi x13, x5, 0 /* RHO_PRIME_0 (RHO_PRIME share 0) */
  addi x14, x6, 0 /* RHO_PRIME_1 (RHO_PRIME share 1) */
  addi x15, x7, 0 /* KAPPA */

  /* Zeroize the output DMEM locations just to be safe. */
  addi x20, x10, 0
  addi x21, x0, 256
  jal x1, zeroize

  addi x20, x11, 0
  addi x21, x0, 256
  jal x1, zeroize

  /* Loop indices for the `expand_a` and `expand_mask`. */
  addi x16, x0, 0 /* r */
  addi x17, x0, 0 /* s */

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
  loopi 7, 38    /* SCA_TEST_REPLACE: loopi 1, 38 */
    /* Expand polynomials Y0[s] and Y1[s] and store them in slots 1 and 2. */
    addi x2, x8, 1024 /* Slot 1 */
    addi x3, x9, 0    /* Slot 2 */
    addi x4, x13, 0
    addi x5, x14, 0
    addi x6, x15, 0
    addi x7, x17, 0
    jal x1, expand_mask

    /* Compute NTT(Y0[s]). */
    addi x2, x8, 1024
    addi x3, x8, 1024
    jal x1, ntt

    /* Compute NTT(Y1[s]). */
    addi x2, x9, 0
    addi x3, x9, 0
    jal x1, ntt

    loopi 8, 18    /* SCA_TEST_REPLACE: loopi 1, 18 */
      /* Expand polynomial A[r][s] and store it at slot 0. */
      addi x2, x8, 0
      addi x3, x12, 0
      addi x4, x16, 0
      addi x5, x17, 0
      jal x1, expand_a

      /* W0[r] += A[r][s] * NTT(Y0[s]). */
      addi x2, x8, 0    /* Slot 0 */
      addi x3, x8, 1024 /* Slot 1 */
      addi x4, x10, 0
      addi x5, x10, 0
      jal x1, poly_mul_add

      /* W1[r] += A[r][s] * NTT(Y1[s]). */
      addi x2, x8, 0 /* Slot 0 */
      addi x3, x9, 0 /* Slot 2 */
      addi x4, x11, 0
      addi x5, x11, 0
      jal x1, poly_mul_add

      /* Increment r and advance output addresses. */
      addi x16, x16, 1
      addi x10, x10, 1024
      addi x11, x11, 1024
      /* End of loop */

    /* Reset r and increment s. */
    addi x16, x0, 0
    addi x17, x17, 1

    /* Reset the output addresses, i.e., subtract 8192. */
    addi x20, x0, 1024
    slli x20, x20, 3    /* SCA_TEST_REPLACE: slli x20, x20, 0 */
    sub x10, x10, x20
    sub x11, x11, x20
    /* End of loop */

  /* Map the result polynomials back to the time domain. */
  loopi 8, 8    /* SCA_TEST_REPLACE: loopi 1, 8 */
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
  loopi 8, 10    /* SCA_TEST_REPLACE: loopi 1, 10 */
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
 * 64-byte `expand_mask` seed RHO_PRIME is assumed to be passed as two Boolean
 * shares and KAPPA is a 2-byte value (in a 32-byte DMEM region). The S1 vector
 * is assumed to be passed in encoded form, i.e., as two 672-byte Boolean
 * shares.
 *
 * Each derived signature polynomial Z[i] undergoes a secure infinity norm
 * check |Z[i]|_inf < 2^19 - BETA before being unmasked.
 *
 * @param[in] x2:  DMEM address of the first share of RHO_PRIME seed.
 * @param[in] x3:  DMEM address of the second share of RHO_PRIME seed.
 * @param[in] x4:  DMEM address of KAPPA.
 * @param[in] x5:  DMEM address of the challenge polynomial C in NTT domain.
 * @param[in] x6:  DMEM address of the first share of the encoded vector S1.
 * @param[in] x7:  DMEM address of the second share of the encoded vector S1.
 * @param[in] x8:  DMEM address of the vectorized bound 2^19 - BETA (32 bytes).
 * @param[in] x9:  DMEM address of the resulting signature vector Z.
 * @param[in] x10: DMEM address of the polynomial slots (slots 0-3 are used).
 * @param[out] w0: 2^256-1 if the norm check passes, 0 otherwise.
 */
compute_z:
  /* Save address of slot 2 for easier access later. */
  addi x11, x10, 2047
  addi x11, x11, 1

  /* Save DMEM address pointers. */
  addi x12, x2, 0 /* RHO_PRIME_0 (RHO_PRIME share 0) */
  addi x13, x3, 0 /* RHO_PRIME_1 (RHO_PRIME share 1) */
  addi x14, x4, 0 /* KAPPA */
  addi x15, x5, 0 /* NTT(C) */
  addi x16, x6, 0 /* S1_0_enc (encoded S1 share 0) */
  addi x17, x7, 0 /* S1_1_enc (encoded S1 share 1) */

  /*
   * Do not save those address pointers which are not overwritten:
   *   x8:  Bound
   *   x9:  Z
   *   x10: Slots
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
  addi x2, x10, 0    /* Slot 0 */
  addi x3, x10, 1024 /* Slot 1 */
  addi x4, x8, 0
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
  addi x2, x0, 7    /* SCA_TEST_REPLACE: addi x2, x0, 1 */
  bne x18, x2, _compute_z_norm_check_loop

  /*
   * Part 2: Compute all the Z[s] polynomials.
   */

  /* Reset the loop index s and the S1 pointers. */
  addi x18, x0, 0
  addi x16, x16, -672    /* SCA_TEST_REPLACE: addi x16, x16, -96 */
  addi x17, x17, -672    /* SCA_TEST_REPLACE: addi x17, x17, -96 */

  loopi 7, 9    /* SCA_TEST_REPLACE: loopi 1, 9 */
    /* Compute the arithmetic shares of Z[s]. */
    jal x1, _compute_z_kernel

    /* At this point, due to the passed infinity norm check, Z0 and Z1 are not
       considered sensitive anymore and can be unmasked (see Section 3.2 in [1]).
         Z[s] = D0 + D1 (unmasking). */
    addi x2, x10, 0    /* Slot 0 */
    addi x3, x10, 1024 /* Slot 1 */
    addi x4, x9, 0
    jal x1, sec_unmask

    /* Increment s, advance S1 and Z pointers. */
    addi x18, x18, 1
    addi x16, x16, 96
    addi x17, x17, 96
    addi x9, x9, 1024
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
  addi x2, x10, 0    /* Slot 0 */
  addi x3, x10, 1024 /* Slot 1 */
  addi x4, x12, 0
  addi x5, x13, 0
  addi x6, x14, 0
  addi x7, x18, 0
  jal x1, expand_mask

  /* Decode S1_0_enc[s] and S1_1_enc[s] as arithmetic shares into slots 2 and 3. */
  addi x2, x16, 0
  addi x3, x17, 0
  addi x4, x11, 0    /* Slot 2 */
  addi x5, x11, 1024 /* Slot 3 */
  jal x1, decode_s

  /* A0 = NTT(S1_0[s]). */
  addi x2, x11, 0
  addi x3, x11, 0
  jal x1, ntt

  /* A1 = NTT(S1_1[s]). */
  addi x2, x11, 1024
  addi x3, x11, 1024
  jal x1, ntt

  /* B0 = NTT(C) * A0 = NTT(C) * S1_0[s]. */
  addi x2, x15, 0
  addi x3, x11, 0
  addi x4, x11, 0
  jal x1, poly_mul

  /* B1 = NTT(C) * A1 = NTT(C) * S1_1[s]. */
  addi x2, x15, 0
  addi x3, x11, 1024
  addi x4, x11, 1024
  jal x1, poly_mul

  /* C0 = INTT(B0) = INTT(NTT(C) * S1_0[s]). */
  addi x2, x11, 0
  addi x3, x11, 0
  jal x1, intt

  /* C1 = INTT(B1) = INTT(NTT(C) * S1_1[s]). */
  addi x2, x11, 1024
  addi x3, x11, 1024
  jal x1, intt

  /* D0 = Y0[s] + C0 = Y0[s] + INTT(NTT(C) * S1_0[s]). */
  addi x2, x10, 0 /* Slot 0 */
  addi x3, x11, 0 /* Slot 2 */
  addi x4, x10, 0
  jal x1, poly_add

  /* D1 = Y1[s] + C1 = Y1[s] + INTT(NTT(C) * S1_1[s]). */
  addi x2, x10, 1024 /* Slot 1 */
  addi x3, x11, 1024 /* Slot 3 */
  addi x4, x10, 1024
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
  addi x2, x0, 8    /* SCA_TEST_REPLACE: addi x2, x0, 1 */
  bne x15, x2, _compute_r0_loop

  /* Reset the R0[s] address pointers. */
  li x2, 8192    /* SCA_TEST_REPLACE: li x2, 1024 */
  sub x10, x10, x2
  sub x11, x11, x2

  /* At this point, due to the passed infinity norm check, D0 and D1 are not
     considered sensitive anymore and can be unmasked (see Section 3.2 in [1]).
       R0[s] = D0 + D1 (unmasking). */
  loopi 8, 6    /* SCA_TEST_REPLACE: loopi 1, 6 */
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

/**
 * Compute the X0 vector.
 *
 * The routine computes X0 = R0 + INTT(NTT(C) * NTT(T0)) through which the hint
 * vector H is derived (see `make_hint`). The T0 polynomials are assumed to be
 * passed in encoded form and are decoded on-the-fly (see `decode_t0`). The
 * DMEM location of R0 is overwritten with X0.
 *
 * @param[in] x2: DMEM address of the R0 vector and the resulting X0 vector.
 * @param[in] x3: DMEM address of the challenge polynomial NTT(C).
 * @param[in] x4: DMEM address of the encoded T0 vector (3328 bytes).
 * @param[in] x5: DMEM address of a polynomial slot.
 */
compute_x0:
  /* Save DMEM address pointers. */
  addi x6, x2, 0 /* R0 */
  addi x7, x3, 0 /* NTT(C) */
  addi x8, x4, 0 /* T0_enc */
  addi x9, x5, 0 /* Slot */

  /*
   * Compute the X0[r] polynomials for 0 <= r < 8 with the following algorithm:
   *
   * for r in [0, 7]:
   *   T0[r] = decode_t0(T0_enc[r])
   *   A = NTT(T0[r])
   *   B = NTT(C) * A
   *   C = INTT(B)
   *   X0[r] = R0[r] + C
   * endfor
   */
  loopi 8, 19    /* SCA_TEST_REPLACE: loopi 1, 19 */
    /* Decode T0[r] into the polynomial slot. */
    addi x2, x8, 0
    addi x3, x9, 0
    jal x1, decode_t0

    /* A = NTT(T0[r]). */
    addi x2, x9, 0
    addi x3, x9, 0
    jal x1, ntt

    /* B = NTT(C) * A = NTT(C) * NTT(T0[r]). */
    addi x2, x7, 0
    addi x3, x9, 0
    addi x4, x9, 0
    jal x1, poly_mul

    /* C = INTT(B) = INTT(NTT(C) * NTT(T0[r])). */
    addi x2, x9, 0
    addi x3, x9, 0
    jal x1, intt

    /* X0[r] = R0[r] + C = R0[r] + INTT(NTT(C) * NTT(T0[r])). */
    addi x2, x6, 0
    addi x3, x9, 0
    addi x4, x6, 0
    jal x1, poly_add

    /* Advance address pointers. */
    addi x6, x6, 1024
    addi x8, x8, 416
    /* End of loop */

  ret

/**
 * Compute the hint vector H.
 *
 * Given the vector X0 = W0 + C * T0 and the encoded vector W1, this routine
 * derives the hint vector H according to the `MakeHint` function (Algorithm 39)
 * of FIPS-204. The DMEM location of X0 is overwritten with H.
 *
 * @param[in] x2: DMEM addresss of the X0 vector and resulting hint vector H.
 * @param[in] x3: DMEM address of the encoded W1 vector (1024 bytes).
 * @param[in] x4: DMEM address of a polynomial slot.
 */
make_hint:
  /* Save DMEM address pointers. */
  addi x5, x2, 0 /* X0 */
  addi x6, x3, 0 /* W1 */
  addi x7, x4, 0 /* Slot */

  /* Set up WDR pointers. */
  addi x8, x0, 3
  addi x9, x0, 4

  /*
   * Hint rationale:
   *
   * Assume a ML-DSA variant where the key vector T is *NOT* decomposed into
   * lower and higher-bit polynomials T0 and T1. It is easy to see that if
   * the signer computes the W1 vector as HighBits(A * Y) = HighBits(W), then
   * the verifier can recompute W1 = HighBits(A * Y) as
   *
   *   A * Z - C * T
   *    = A * (Y + C * S1) - C * (A * S1 + S2)
   *    = A * Y + A * C * S1 - A * C * S1 - C * S2
   *    = A * Y - C * S2
   *
   *   HighBits(A * Y - C * S2) = HighBits(A * Y) = HighBits(W) = W1
   *
   * The last relation holds because C * S2 contains only small-norm
   * coefficients that do not cause any bit flips in the high bits of each
   * coefficient.
   *
   * Now in the standardized variant of ML-DSA, the verifier is not given the
   * full vector T but only T1, i.e., the vector of the higher-bits of T.
   * Hence, W1 cannot be recomputed correctly anymore since
   *
   *   A * Z - C * (2^D * T1)
   *     = A * Z - C * T + C * T0
   *     = A * Y - C * S2 + C * T0
   *     = W - C * S2 + C * T0
   *     = (2*GAMMA2 * W1 + W0 - C * S2) + C * T0
   *     = (2*GAMMA2 * W1 + R0) + C * T0
   *
   * In other words, the recomputation of W1 is wrong in all coefficients where
   * the addition of C * T0 caused an overflow in R0 = W0 - C * S2 that spilled
   * into W1. The polynomials of the hint vector indidicate which coefficients
   * have overflown and need to be corrected during the verification.
   */

  /* Calculate the hint polynomials H[r] for 0 <= r < 8. */
  loopi 8, 32    /* SCA_TEST_REPLACE: loopi 1, 32 */
    /* Decode W1[r] into the polynomial slot. */
    addi x2, x6, 0
    addi x3, x7, 0
    jal x1, decode_w1

    /* Prepare some constants for the loop below. */

    /* w0 = GAMMA2 = (Q - 1) / 32 = 0x3ff00. */
    bn.not w0, w31
    bn.shv.8s w0, w0 >> 22
    bn.shv.8s w0, w0 << 8

    /* w1 = Q = 0x7fe001. */
    bn.not w1, w31
    bn.shv.8s w2, w1 >> 31
    bn.shv.8s w1, w1 >> 22
    bn.shv.8s w1, w1 << 13
    bn.or w1, w1, w2

    /* w2 = (Q - 1) / 2. */
    bn.shv.8s w2, w1 >> 1

    /*
     * A coefficient in the hint polynomial is 1 if at least one of the
     * conditions met (assuming x0 = x0 mod^+- Q):
     *
     *   1. x0 > GAMMA2
     *   2. x0 < -GAMMA2
     *   3. x0 == -GAMMA2 && w1 != 0
     *
     * In other words, if any of the three conditions is met, then the addition
     * of C * T0 to W0 W0 caused an overflow in one or more coefficients in W0
     * that spilled into W1.
     */

    /*
     * Iterate over the polynomials X0[r] and W1[r] in steps of 8 coefficients
     * and process them in a vectorized fashion.
     */
    loopi 32, 17
      /* Load 8 coefficients of X0[r] and W1[r] into w3 and w4. */
      bn.lid x8, 0(x5)
      bn.lid x9, 0(x7++)

      /*
       * Calculate x0 mod^+- Q (reduction):
       *
       *   x0 = x0 - (((((Q - 1) / 2) - x0) >>> 31) & Q),
       *
       * with >>> being the arithmetic right shift operator.
       *
       * XXX: Open question, can the hint be computed without the reduction?
       */
      bn.subv.8s w5, w2, w3
      bn.shv.8s w5, w5 >> 31
      bn.subv.8s w5, w31, w5
      bn.and w5, w5, w1
      bn.subv.8s w3, w3, w5

      /* w5 = 1 if w1 != 0, else 0. */
      bn.subv.8s w5, w31, w4
      bn.or w5, w5, w4
      bn.shv.8s w5, w5 >> 31

      /*
       * Let t = x0 + GAMMA2, then the following relation holds pertaining to
       * conditions 2 and 3.
       *
       *   Cond2 || Cond3
       *   <-> (x0 < -GAMMA2) || (x0 == -GAMMA2 && w1 != 0)
       *   <-> (t < 0) || (t == 0 && w1 != 0)
       *   <-> (t - (w1 != 0)) < 0
       */

      /* w6 = 1 if (t - (w1 != 0)) < 0, else 0 (Cond 2 || Cond 3). */
      bn.addv.8s w6, w3, w0
      bn.subv.8s w6, w6, w5
      bn.shv.8s w6, w6 >> 31

      /* w5 = 1 if x0 > GAMMA2, else 0 (Cond 1). */
      bn.subv.8s w5, w0, w3
      bn.shv.8s w5, w5 >> 31

      /* w3 = 1, if (Cond 1 || Cond 2 || Cond 3), else 0. */
      bn.or w3, w5, w6

      /* Store the calculated hint vector back to DMEM. */
      bn.sid x8, 0(x5++)
      /* End of loop */

    /* Advance the W1 pointer and reset the slot pointer. */
    addi x6, x6, 128
    addi x7, x7, -1024
    /* End of loop */

  ret

/**
 * Check the Hamming weight of the hint vector H.
 *
 * All the hint polynomials must not contain more than OMEGA = 75 coefficients
 * that are set to 1. This routine calculate this Hamming weight and compares
 * to the bound OMEGA.
 *
 * @param[in] x2: DMEM address of the hint vector H (8 * 1024 bytes).
 * @param[out] w0, 2^256 - 1 if HW(H) <= OMEGA, else 0.
 */
hw_check_hint:
  bn.addi w1, w31, 0 /* 8 parallel counters. */
  bn.addi w2, w31, 0x3ff /* Mask */

  /*
   * Accumulate the eight parallel counters by looping over all H[r] in steps
   * of eight coefficients at a time.
   */
  loopi 8, 4    /* SCA_TEST_REPLACE: loopi 1, 4 */
    loopi 32, 2
      bn.lid x0, 0(x2++)
      bn.addv.8s w1, w1, w0
      /* End of loop */
    nop
    /* End of loop */

  /*
   * Fold the 8 counters into one.
   */

  /* Final number of 1-coefficients in H. */
  bn.addi w0, w31, 0
  loopi 8, 3
    bn.and w3, w1, w2
    bn.add w0, w0, w3
    bn.rshi w1, w31, w1 >> 32
    /* End of loop */

  /*
   * w0 = 2^256 - 1 if 75 - w0 >= 0 (MSB of 75 - w0 not set).
   */
  bn.addi w2, w31, 75
  bn.not w3, w31

  bn.cmp w2, w0, FG0
  bn.sel w0, w31, w3, FG0.M

  ret

/**
 * Compress the hint vector H.
 *
 * This routine takes the fully expanded hint vector H (8 * 1024 bytes) and
 * compresses it to 83 bytes in a 96-byte allocated region. This is an
 * implementation of the `HintBitPack` function (Algorithm 20) of FIPS-204.
 * For a detailed explanation of this compressed hint format see the
 * `HintBitUnpack` function (Algorithm 21) of FIPS-204.
 *
 * @param[in] x2: DMEM address of the expanded hint vector H (8 * 1024 bytes).
 * @param[in] x3: DMEM address of the compressed hint 83 bytes in 96-byte region.
 * @param[in] x4: DMEM address of a polynomial slot (1024 bytes).
 */
compress_hint:
  /* Zeroize the polynomial slot just to be safe. */
  addi x20, x4, 0
  addi x21, x0, 32
  jal x1, zeroize

  /* Indices. */
  addi x5, x0, 0 /* i */
  addi x6, x0, 0 /* j */
  addi x7, x0, 0 /* index */

  /*
   * Part 1: Compress the hint down to a (83 * 4)-byte region where each of the
   * 83 entries occupies a 4-byte DMEM word in the slot. The following
   * algorithm is implemented:
   *
   * index = 0
   * for i in [0, 7]:
   *   for j in [0, 255]:
   *     if H[i][j] == 1:
   *       Slot[index * 4] = j
   *       index += 1
   *   endfor
   *   Slot[(75 + i) * 4] = index
   * endfor
   */
  loopi 8, 16    /* SCA_TEST_REPLACE: loopi 1, 16 */
    loopi 256, 8
      /* x8 = H[i][j]. */
      lw x8, 0(x2)

      /* Skip if H[i][j] == 0. */
      beq x8, x0, _compress_hint_skip_coeff

      /* Slot[index * 4] = x9. */
      slli x10, x7, 2
      add x10, x4, x10
      sw x6, 0(x10)

      /* index += H[i][j]. */
      add x7, x7, x8

_compress_hint_skip_coeff:

      /* Increment j and H address pointer. */
      addi x6, x6, 1
      addi x2, x2, 4
      /* End of loop */

    /* Slot[(75 + i) * 4] = index. */
    addi x8, x0, 75
    add x8, x8, x5
    slli x8, x8, 2
    add x8, x8, x4
    sw x7, 0(x8)

    /* Increment i and reset j. */
    addi x5, x5, 1
    addi x6, x0, 0
    /* End of loop */

  /*
   * Part 2: Compress the (83 * 4)-byte hint further to its final 83-byte form.
   */

  /* Zeroize the output region just to be safe. */
  addi x20, x3, 0
  addi x21, x0, 3
  jal x1, zeroize

  /* Set up input/output DMEM pointers. */
  addi x5, x3, 0 /* H_enc */
  addi x6, x4, 0 /* Slot */

  /* We iterate 21 * 4 = 84 times with the 84th coefficient being ignored in
     the output. */
  loopi 21, 9
    /* 4-byte word accumulator. */
    addi x7, x0, 0

    /* Load 4 elements and shift them into the accumulator. */
    loopi 4, 5
      /* Load one element and place it at the most signficant byte of w8. */
      lw x8, 0(x6)
      slli x8, x8, 24

      /* Add the element in w8 to w7. */
      srli x7, x7, 8
      or x7, x7, x8

      addi x6, x6, 4
      /* End of loop */

    /* Store the accumulated 4 elements into the output location. */
    sw x7, 0(x5)
    addi x5, x5, 4
    /* End of loop */

  ret

/* High-level operations for the ML-DSA-87 verify function. */

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
  loopi 7, 11
    addi x2, x14, 0
    addi x3, x14, 0
    jal_fi ntt, 977 /* 7 instructions. */
    addi x14, x14, 1024
    /* End of loop */

  /* Indices r, s for the expansion of A. */
  addi x14, x0, 0
  addi x15, x0, 0

  /* Temp address pointers for Z and W_approx. */
  addi x16, x9, 0
  addi x17, x12, 0

  /* Compute W_approx = A * NTT(Z). */
  loopi 8, 24
    loopi 7, 19
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
      jal_fi poly_mul_add, 252  /* 7 instructions. */

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
  jal_fi ntt, 977 /* 7 instructions. */

  /* Compute W_approx[i] = INTT((A * NTT(Z))[i] - NTT(C) * NTT(T1[i] * 2^d)). */
  loopi 8, 64
    /* Decode T1[i] into slot 0. */
    addi x2, x11, 0
    addi x3, x13, 0
    jal_fi decode_t1, 1232 /* 7 instructions. */

    /* Shift left: T1[i] * 2^d. */
    addi x2, x13, 0
    addi x3, x13, 0
    jal_fi shift_left, 106 /* 7 instructions. */

    /* Map T1[i] * 2^d into NTT domain in-place. */
    addi x2, x13, 0
    addi x3, x13, 0
    jal_fi ntt, 977 /* 7 instructions. */

    /* Calculate T1[i] = c * T1[i]. */
    addi x2, x10, 0
    addi x3, x13, 0
    addi x4, x13, 0
    jal_fi poly_mul, 179 /* 7 instructions. */

    /* Calculate W[i] = W[i] - c * T1[i]. */
    addi x2, x14, 0
    addi x3, x13, 0
    addi x4, x14, 0
    jal_fi poly_sub, 147 /* 7 instructions. */

    /* Map the result back to the time domain. */
    addi x2, x14, 0
    addi x3, x14, 0
    jal_fi intt, 1042 /* 7 instructions. */

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
  loopi 8, 35
    /* Decompose W[i] and put the high bits in the output location and the low
      bits into slot 0. */
    addi x2, x6, 0
    addi x3, x8, 0 /* r0 */
    addi x4, x6, 0 /* r1 */
    jal_fi decompose, 513 /* 7 instructions. */

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
  loopi 8, 10
    jal_fi encode_w1, 690 /* 7 instructions. */
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

/**
 * Check the Hamming weight of the challenge polynomial c (scalar loop).
 *
 * The challenge polynomial must contain exactly 60 non-zero coefficients.
 * This routine calculates this Hamming weight coefficient-by-coefficient
 * across the 256 coefficients and asserts that it equals 60.
 *
 * @param[in] x2: DMEM address of the challenge polynomial c (1024 bytes).
 * @param[out] w0: 2^256 - 1 if HW(c) == 60, else 0.
 */
check_hw_c:
  li x3, 0  /* Counter for non-zero coefficients */

  /*
   * Loop over all 256 32-bit coefficients.
   */
  loopi 256, 6
    lw x4, 0(x2)
    addi x2, x2, 4
    sub x5, x0, x4      /* x5 = -c_i */
    or x5, x5, x4       /* x5 = c_i | (-c_i) (MSB is 1 iff c_i != 0) */
    srli x5, x5, 31     /* x5 = 1 if c_i != 0, else 0 */
    add x3, x3, x5      /* counter += (c_i != 0) */

  /*
   * Check if counter (x3) == 60.
   * If x3 == 60: return w0 = 2^256 - 1.
   * If x3 != 60: return w0 = 0.
   */
  bn.addi w0, w31, 0    /* Default w0 = 0 */
  li x4, 60
  bne x3, x4, _check_hw_c_end

  bn.not w0, w31        /* w0 = 2^256 - 1 */

_check_hw_c_end:
  ret
