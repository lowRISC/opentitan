/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* High-level operations for the ML-DSA key generation function. */

.globl sample_s

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
