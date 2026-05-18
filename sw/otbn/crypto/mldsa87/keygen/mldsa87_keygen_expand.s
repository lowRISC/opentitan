/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial expansion routines for ML-DSA-87 keygen. */

.globl expand_s1
.globl expand_s2

.text

/**
 * Expand a secret-key polynomial.
 *
 * Given an index 0 <= r < 7, and a 66-byte Boolean-shared seed rho, this
 * routine samples a polynomial S[r] of the secret key vectors S1 and S2. This
 * is an implementation of the `ExpandS` function (Algorithm 33) of FIPS-204.
 *
 * Bytes 64 and 65 of rho shall be set to 0.
 *
 * Note that although the seed rho is a Boolean-shared value of size 66 bytes,
 * it shall be provided in two 96-byte allocated regions.
 *
 * @param[in] x2: DMEM address of the first Boolean share of rho (66 bytes).
 * @param[in] x3: DMEM address of the second Boolean share of rho (66 bytes).
 * @param[in] x4: DMEM address of the first arithmetic share of the sampled S.
 * @param[in] x5: DMEM address of the second arithmetic share of the sampled S.
 * @param[in] x6: Index r, 0 <= r < 7.
 */

/* The only difference between sampling a S1 polynomial and a sampling a S2
   polynomial lies in the value of bytes 64 and 65 of rho which is r for S1
   and r * L for S2. */
expand_s2:
  addi x20, x0, 7
  jal x0, _expand_s
expand_s1:
  addi x20, x0, 0
_expand_s:
  /* Set rho[65:64] = {r, r + L}. */
  add x20, x20, x6
  sw x20, 64(x2)

  jal x1, rej_bounded_poly

  /* Reset rho[65:64] = 0. */
  sw x0, 64(x2)

  ret
