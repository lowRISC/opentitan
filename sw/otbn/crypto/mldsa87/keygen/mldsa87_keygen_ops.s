/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* High-level operations for the ML-DSA key generation function. */

.globl sample_s
.globl compute_t
.globl encode_t
.globl hash_seed
.globl hash_pk

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
  loopi 7, 14
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
  loopi 8, 14
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

  loopi 7, 38
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

    loopi 8, 18
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
    slli x20, x20, 3
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

  loopi 8, 23
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
  loopi 8, 18
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
  /* Xi[32] = K = 8, Xi[33] = L = 7. */
  li x9, 0x00000708
  sw x9, 32(x2)

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
