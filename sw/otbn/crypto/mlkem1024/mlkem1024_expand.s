/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Matrix and noise expansion routines (ExpandA, ExpandPRF) for ML-KEM-1024. */

.globl expand_a
.globl expand_prf

.text

/**
 * Expand matrix polynomial entry A[i][j] for ML-KEM-1024 using SHAKE128 XOF.
 *
 * Implements matrix expansion A[i][j] for ML-KEM-1024 per FIPS 203 Section 5.1 / Algorithm 7.
 * Absorbs 34-byte message B = rho || j || i into SHAKE128 hardware XOF (where
 * rho is 32 bytes, j is 1 byte column index, and i is 1 byte row index),
 * squeezes 512 bytes into _expand_buf, and calls sample_ntt_poly to sample 256 coefficients mod 3329.
 *
 * @param[in]  x2: DMEM address of 32-byte seed rho (in a 64-byte allocated space).
 * @param[in]  x3: Column index j (0 <= j <= 3).
 * @param[in]  x4: Row index i (0 <= i <= 3).
 * @param[out] x5: DMEM output address for sampled matrix polynomial (256 32-bit words).
 *
 * Clobbered Vector Registers: w0, w29, w30.
 */
expand_a:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x20, x21, x22, x23, x24
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Copy 32-byte rho from x2 to _expand_buf and append j||i at offset 32 */
  la   x21, _expand_buf
  bn.lid x0, 0(x2)
  bn.sid x0, 0(x21)
  bn.xor w0, w0, w0
  bn.sid x0, 32(x21)
  slli x20, x4, 8
  add  x20, x20, x3
  sw   x20, 32(x21)

  /* Initialize SHAKE128 hardware XOF */
  jal x1, xof_shake128_init

  /* Absorb 34 bytes of rho || j || i */
  addi x20, x0, 34  /* length 34 bytes */
  addi x22, x0, 0   /* unmasked */
  jal  x1, xof_absorb

  /* Finish absorb and process */
  jal x1, xof_process

  /* Squeeze 16 chunks of 32 bytes (512 bytes total) into _expand_buf */
  la   x20, _expand_buf
  addi x23, x0, 0
  addi x24, x0, 16
_expand_a_squeeze_loop:
  jal  x1, xof_squeeze32
  bn.xor w0, w29, w30
  bn.sid x0, 0(x20++)
  addi x23, x23, 1
  bne  x23, x24, _expand_a_squeeze_loop

  /* Finish XOF session */
  jal x1, xof_finish

  /* Call sample_ntt_poly(x2=_expand_buf, x3=x5) */
  la x2, _expand_buf
  addi x3, x5, 0
  jal x1, sample_ntt_poly

  /* Restore registers from stack. */
  .irp reg, x24, x23, x22, x21, x20, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Expand noise polynomial for ML-KEM-1024 using SHAKE256 PRF (ExpandPRF).
 *
 * Implements noise expansion per FIPS 203 Section 4.1 / Algorithm 8 (SamplePolyCBD_eta).
 * Absorbs 33-byte message B = s || N into SHAKE256 hardware XOF (where s is
 * 32 bytes seed and N is 1 byte nonce), squeezes 128 bytes into _expand_buf,
 * and calls sample_cbd_poly.
 *
 * @param[in]  x2: DMEM address of 32-byte seed s (in a 64-byte allocated space).
 * @param[in]  x3: Nonce N (0 <= N <= 255).
 * @param[out] x4: DMEM output address for sampled noise polynomial (256 32-bit words).
 *
 * Clobbered Vector Registers: w0, w29, w30.
 */
expand_prf:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x20, x21, x22, x23, x24
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Initialize 32-byte slot at offset 32 to guarantee valid 256-bit DMEM ECC integrity for bn.lid in xof_absorb */
  bn.xor w0, w0, w0
  bn.sid x0, 32(x2)

  /* Append Nonce byte N to seed s at offset 32 */
  addi x21, x2, 0   /* save s address in x21 */
  sw   x3, 32(x21)

  /* Initialize SHAKE256 hardware XOF */
  jal x1, xof_shake256_init

  /* Absorb 33 bytes of s || N */
  addi x20, x0, 33  /* length 33 bytes */
  addi x22, x0, 0   /* unmasked */
  jal  x1, xof_absorb

  /* Finish absorb and process */
  jal x1, xof_process

  /* Squeeze 4 chunks of 32 bytes (128 bytes total) into _expand_buf */
  la   x20, _expand_buf
  addi x23, x0, 0
  addi x24, x0, 4
_expand_prf_squeeze_loop:
  jal  x1, xof_squeeze32
  bn.xor w0, w29, w30
  bn.sid x0, 0(x20++)
  addi x23, x23, 1
  bne  x23, x24, _expand_prf_squeeze_loop

  /* Finish XOF session */
  jal x1, xof_finish

  /* Call sample_cbd_poly(x2=_expand_buf, x3=x4) */
  la x2, _expand_buf
  addi x3, x4, 0
  jal x1, sample_cbd_poly

  /* Restore registers from stack. */
  .irp reg, x24, x23, x22, x21, x20, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret
