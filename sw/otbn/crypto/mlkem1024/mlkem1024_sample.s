/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial sampling subroutines (SampleNTT, SamplePolyCBD) for ML-KEM-1024 (q = 3329). */

.globl sample_ntt_poly
.globl sample_cbd_poly

.text

/**
 * Rejection sampling for uniform polynomial coefficients modulo q = 3329 (SampleNTT).
 *
 * Implements Algorithm 7 (SampleNTT) of FIPS 203. Parses a byte stream B into
 * 3-byte groups [b0, b1, b2] and extracts two 12-bit candidate integers:
 *   d1 = b0 + 256 * (b1 & 0x0F)
 *   d2 = (b1 >> 4) + 16 * b2
 *
 * Candidates < 3329 are accepted as valid polynomial coefficients in the NTT domain.
 * Repeats parsing until 256 coefficients are collected.
 *
 * @param[in]  x2: DMEM address of byte stream input.
 * @param[out] x3: DMEM output address for sampled polynomial (256 32-bit words, 1024 bytes).
 *
 */
sample_ntt_poly:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x6, x7, x8, x9, x11, x13
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  li   x4, 3329      /* Modulus q = 3329 */
  li   x5, 256       /* Remaining coefficient count (256 to 0) */
  li   x13, 0xFFF    /* 12-bit mask (4095) */

_sample_ntt_loop:
  /* Load 12 bytes (3 words) from DMEM input stream. */
  lw   x6, 0(x2)     /* W0 */
  lw   x7, 4(x2)     /* W1 */
  lw   x8, 8(x2)     /* W2 */
  addi x2, x2, 12

  /* Group 0: W0 */
  /* Candidate 0: W0 & 0xFFF */
  and  x9, x6, x13
  sub  x11, x9, x4
  srli x11, x11, 31
  beq  x11, x0, 1f
  sw   x9, 0(x3)
  addi x3, x3, 4
  addi x5, x5, -1
  beq  x5, x0, _sample_ntt_done
1:

  /* Candidate 1: (W0 >> 12) & 0xFFF */
  srli x9, x6, 12
  and  x9, x9, x13
  sub  x11, x9, x4
  srli x11, x11, 31
  beq  x11, x0, 2f
  sw   x9, 0(x3)
  addi x3, x3, 4
  addi x5, x5, -1
  beq  x5, x0, _sample_ntt_done
2:

  /* Candidate 2: (W0 >> 24) | (W1 << 8) & 0xFFF */
  srli x9, x6, 24
  slli x11, x7, 8
  or   x9, x9, x11
  and  x9, x9, x13
  sub  x11, x9, x4
  srli x11, x11, 31
  beq  x11, x0, 3f
  sw   x9, 0(x3)
  addi x3, x3, 4
  addi x5, x5, -1
  beq  x5, x0, _sample_ntt_done
3:

  /* Candidate 3: (W1 >> 4) & 0xFFF */
  srli x9, x7, 4
  and  x9, x9, x13
  sub  x11, x9, x4
  srli x11, x11, 31
  beq  x11, x0, 4f
  sw   x9, 0(x3)
  addi x3, x3, 4
  addi x5, x5, -1
  beq  x5, x0, _sample_ntt_done
4:

  /* Candidate 4: (W1 >> 16) & 0xFFF */
  srli x9, x7, 16
  and  x9, x9, x13
  sub  x11, x9, x4
  srli x11, x11, 31
  beq  x11, x0, 5f
  sw   x9, 0(x3)
  addi x3, x3, 4
  addi x5, x5, -1
  beq  x5, x0, _sample_ntt_done
5:

  /* Candidate 5: (W1 >> 28) | (W2 << 4) & 0xFFF */
  srli x9, x7, 28
  slli x11, x8, 4
  or   x9, x9, x11
  and  x9, x9, x13
  sub  x11, x9, x4
  srli x11, x11, 31
  beq  x11, x0, 6f
  sw   x9, 0(x3)
  addi x3, x3, 4
  addi x5, x5, -1
  beq  x5, x0, _sample_ntt_done
6:

  /* Candidate 6: (W2 >> 8) & 0xFFF */
  srli x9, x8, 8
  and  x9, x9, x13
  sub  x11, x9, x4
  srli x11, x11, 31
  beq  x11, x0, 7f
  sw   x9, 0(x3)
  addi x3, x3, 4
  addi x5, x5, -1
  beq  x5, x0, _sample_ntt_done
7:

  /* Candidate 7: (W2 >> 20) & 0xFFF */
  srli x9, x8, 20
  and  x9, x9, x13
  sub  x11, x9, x4
  srli x11, x11, 31
  beq  x11, x0, 8f
  sw   x9, 0(x3)
  addi x3, x3, 4
  addi x5, x5, -1
  beq  x5, x0, _sample_ntt_done
8:

  jal  x0, _sample_ntt_loop

_sample_ntt_done:
  /* Restore registers from stack. */
  .irp reg, x13, x11, x9, x8, x7, x6, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Centered Binomial Distribution sampling for noise polynomials (SamplePolyCBD_eta).
 *
 * Implements Algorithm 8 (SamplePolyCBD_eta) of FIPS 203 for eta = 2.
 * Samples 256 noise coefficients from 128 bytes (1024 bits) of PRF stream.
 *
 * For each coefficient i in 0..255:
 *   a = b[4i] + b[4i+1]
 *   b_val = b[4i+2] + b[4i+3]
 *   coeff[i] = (a - b_val) mod 3329
 *
 * @param[in]  x2: DMEM address of 128 PRF bytes (32 32-bit words).
 * @param[out] x3: DMEM output address for sampled polynomial (256 32-bit words, 1024 bytes).
 *
 */
sample_cbd_poly:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x6, x7, x10, x11, x12, x13
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  li   x4, 3329      /* Modulus q = 3329 */
  li   x10, 0x11111111
  li   x11, 0x22222222

  loopi 32, 23
    lw   x5, 0(x2)     /* Load 32-bit word (4 bytes = 8 coefficients) */
    addi x2, x2, 4

    /* Parallel computation of (b0 + b1 + 2 - b2 - b3) for 8 nibbles: */
    and  x12, x5, x10
    srli x6, x5, 1
    and  x13, x6, x10
    add  x12, x12, x13
    add  x12, x12, x11
    srli x6, x5, 2
    and  x13, x6, x10
    srli x6, x5, 3
    and  x6, x6, x10
    add  x13, x13, x6
    sub  x12, x12, x13

    /* Unpack and store 8 coefficients */
    loopi 8, 8
      andi x6, x12, 7
      srli x12, x12, 4
      addi x6, x6, -2
      srai x7, x6, 31
      and  x7, x7, x4
      add  x6, x6, x7
      sw   x6, 0(x3)
      addi x3, x3, 4
      /* End of inner loop */
    nop
    /* End of outer loop */

  /* Restore registers from stack. */
  .irp reg, x13, x12, x11, x10, x7, x6, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret
