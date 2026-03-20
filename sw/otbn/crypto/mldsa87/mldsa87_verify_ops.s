/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* High-level operations for the ML-DSA-87 verify function. */

.globl decode_sig
.globl check_infinity_norm_z

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
