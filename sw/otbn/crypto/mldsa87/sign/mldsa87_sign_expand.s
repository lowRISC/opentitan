/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial expansion routines for ML-DSA-87 sign. */

.globl expand_mask

.text

/**
 * Expand a mask polynomial.
 *
 * Given an index 0 <= r < 7, and a 66-byte Boolean-shared seed rho, this
 * routine samples a polynomial Y[r] of the mask vector Y. This is an
 * implementation of the `ExpandMask` function (Algorithm 34) of FIPS-204.
 *
 * Bytes 64 and 65 shall already contain the the nonce, which is handled
 * externally by the rejection loop.
 *
 * Note that although the seed rho is of size 66 bytes, it shall be provided in
 * two 96-byte allocated regions.
 *
 * @param[in] x2: DMEM address of the first arithmetic share of Y[r].
 * @param[in] x3: DMEM address of the second arithmetic share of Y[r].
 * @param[in] x4: DMEM address of the first Boolean share of rho (66 bytes).
 * @param[in] x5: DMEM address of the second Boolean share of rho (66 bytes).
 * @param[in] x6: Index r, 0 <= r < 7.
 */
expand_mask:
  /* Add r to the two-byte value rho[65]|rho[64] (nonce) of the first share.
     These two trailing bytes do not need to be masked as they are public. */
  lw x20, 64(x4)
  add x20, x20, x6
  sw  x20, 64(x4)

  jal x1, sample_mask_poly

  /* Remove r again from rho[65]|rho[64] to maintain consistency over multiple
     rejection loops. */
  lw x20, 64(x4)
  sub x20, x20, x6
  sw  x20, 64(x4)

  ret
