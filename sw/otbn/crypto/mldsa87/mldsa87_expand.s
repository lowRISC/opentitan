/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial expansion routines. */

.globl expand_a

/**
 * Expand a polynomial of the A matrix.
 *
 * Given indices 0 <= r < 8, 0 <= s < 7 and a 32-byte seed rho, this routine
 * samples a polynomial of the matrix A in the NTT domain. This is an
 * implementation of the `ExpandA` function (Algorithm 32) of FIPS-204. The
 * sampled polynonmial will be stored in packed form at DMEM[x2:x2+768].
 *
 * Note that although the seed rho is of size 32 bytes, it needs to be provided
 * in a 64-byte allocated region.
 *
 * @param[in] x2: DMEM address of the sampled matrix polynomial.
 * @param[in] x3: DMEM address of the 32-byte seed rho.
 * @param[in] x4: Index r, 0 <= r < 8.
 * @param[in] x5: Index s, 0 <= s < 7.
 */
expand_a:
  /* Append indices r and s to the seed rho to create a 34-byte input such that
     rho' = rho | s | r.
     Use scratch register x16. */
  slli x20, x4, 8
  add  x20, x20, x5
  sw x20, 32(x3)

  jal x1, rej_ntt_poly

  ret
