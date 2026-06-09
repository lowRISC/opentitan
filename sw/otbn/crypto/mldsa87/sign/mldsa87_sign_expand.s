/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial expansion routines for ML-DSA-87 sign. */

.globl expand_mask

.text

/**
 * Expand a mask polynomial.
 *
 * Given an index 0 <= r < 7, a 64-byte Boolean-shared seed rho, and 2-byte
 * nonce kappa (in 32-byte DMEM region), this routine samples a polynomial Y[r]
 * of the mask vector Y. This is an implementation of the `ExpandMask` function
 * (Algorithm 34) of FIPS-204.
 *
 * @param[in] x2: DMEM address of the first arithmetic share of Y[r].
 * @param[in] x3: DMEM address of the second arithmetic share of Y[r].
 * @param[in] x4: DMEM address of the first Boolean share of rho (64 bytes).
 * @param[in] x5: DMEM address of the second Boolean share of rho (64 bytes).
 * @param[in] x6: DMEM address of kappa (2 bytes, in 32-byte DMEM region).
 * @param[in] x7: Index r, 0 <= r < 7.
 */
expand_mask:
  /* Add r to kappa. */
  lw x20, 0(x6)
  add x20, x20, x7
  sw  x20, 0(x6)

  jal x1, sample_mask_poly

  /* Subtract r again from kappa to maintain consistency over multiple
     rejection loops. */
  lw x20, 0(x6)
  sub x20, x20, x7
  sw  x20, 0(x6)

  ret
