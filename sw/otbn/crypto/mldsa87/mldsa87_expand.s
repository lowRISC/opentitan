/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.include "mldsa87.inc"

/* Polynomial expansion routines. */

/* Common */
.globl expand_a

/* Keygen */
.globl expand_s1
.globl expand_s2

/* Sign */
.globl expand_mask

.text

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

/* Polynomial expansion routines for ML-DSA-87 keygen. */

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

/* Polynomial expansion routines for ML-DSA-87 sign. */

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
