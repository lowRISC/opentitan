/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* The interface for this file can be accessed through the following symbols.
 * All of them are declared weak in this file, so can be overridden by code
 * that links against this object:
 *
 *   in_mod:   INPUT
 *             384 bytes
 *             The modulus
 *
 *   m0inv:    OUTPUT
 *             384 bytes
 *             The Montgomery constant
 */

.text

/**
 * Computes least significant 256 bits of a 256x256 bit product.
 *
 * Returns c = (a x b) mod (2^256).
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] w2: a, first operand
 * @param[in] w5: b, second operand
 * @param[out] w27: c, result
 *
 * clobbered registers: w27
 * clobbered flag groups: FG0
 */
mul256_low_w2xw5:
  bn.mulqacc.z          w2.0, w5.0,  0
  bn.mulqacc            w2.1, w5.0, 64
  bn.mulqacc.so  w27.L, w2.0, w5.1, 64
  bn.mulqacc            w2.2, w5.0,  0
  bn.mulqacc            w2.1, w5.1,  0
  bn.mulqacc            w2.0, w5.2,  0
  bn.mulqacc            w2.3, w5.0, 64
  bn.mulqacc            w2.2, w5.1, 64
  bn.mulqacc            w2.1, w5.2, 64
  bn.mulqacc.so  w27.U, w2.0, w5.3, 64

  ret

/**
 * Checks whether two wide registers have equal values.
 *
 *   Returns c = 1 if a = b, 0 otherwise.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w6: a, first operand
 * @param[in]  w27: b, second operand
 * @param[out] x4: c, result
 *
 * clobbered registers: x3, x4
 * clobbered Flag Groups: FG0
 *
 */
check_eq_w6w27:
    /* Check if b < a. */
    bn.cmp    w27, w6

    /* Get value from flag register.
         x3 <= (b < a) */
    csrrs     x3, FG0, x0
    andi      x3, x3, 1

    /* Check if a < b. */
    bn.cmp    w6, w27

    /* Get value from flag register.
         x4 <= (a < b) */
    csrrs     x4, FG0, x0
    andi      x4, x4, 1

    /* If b < a or a < b, then a != b; otherwise a = b.
         x4 <= !(b < a | a < b) = (a == b)*/
    or        x4, x4, x3
    xori      x4, x4, 1

    ret

/**
 * Computes the m0_inv Montgomery constant and stores it in DMEM.
 *
 *   Returns m0_inv = (- M') mod (2^256)
 *                    where M' is the modular multiplicative inverse of M.
 *
 * This implementation is based on ALgorithm 3 of "Montgomery Arithmetic from a
 * Software Perspective" (https://eprint.iacr.org/2017/1057). For the purposes
 * of RSA 3072, the parameters w and n from the paper are fixed (w=256, n=12).
 *
 * The result is stored in dmem[m0inv]. This routine runs in variable time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  dmem[in_mod] pointer to first limb of modulus M in dmem
 *
 * clobbered registers: x2 to x4, x9, x16, x26, w2 to w6, w27, w31
 * clobbered Flag Groups: FG0
 */
 .globl compute_m0_inv
compute_m0_inv:
  /* Prepare all-zero register. */
  bn.xor    w31, w31, w31

  /* y = w2 <= 1 */
  bn.addi   w2, w31, 1

  /* i = x2 <= 1 */
  addi   x2, x0, 1

  /* pow2i = w3 <= 2^i = 2 */
  bn.addi   w3, w31, 2

  /* maski = w4 <= 2^(i+1) - 1 = 3 */
  bn.addi   w4, w31, 3

  /* w5 <= M[0] = M mod (2^256) */
  li        x3, 5
  la        x16, in_mod
  bn.lid    x3, 0(x16)

  /* w6 <= 1 */
  bn.addi   w6, w31, 1

  /**
   * Main loop from i=1 to i=255.
   *
   * Invariants:
   *   x2 = i
   *   w2 = y
   *   w3 = 2^i (powi)
   *   w4 = 2^(i+1)-1 (maski)
   *   w5 = M[0] (constant)
   *   w6 = 1    (constant)
   *   y < 2^i
   */
  loopi 255, 8
    /* w27 <= (w2 * w5) mod (2^256)
            = (y * M[0]) mod (2^256) = (M * y) mod (2^256) */
    jal       x1, mul256_low_w2xw5
    /* w27 <= w27 & maski = (M * y) mod (2^(i+1)) */
    bn.and    w27, w27, w4
    /* x4 <= 1 if w27 = 1, 0 otherwise */
    jal       x1, check_eq_w6w27
    /* skip addition if w27 == 1*/
    bne       x4, x0, skip_add
    /* y = w2 <= y + pow2i */
    bn.add    w2, w2, w3
    skip_add:
    /* i = x2 <= i + 1 */
    addi      x2, x2, 1
    /* pow2i = w3 <= pow2i * 2 = 2^i */
    bn.add    w3, w3, w3
    /* maski = w4 <= maski + pow2i = 2^(i+1) - 1 */
    bn.add    w4, w4, w3

  /* m0_inv = w2 <= 2^256 - y = (0 - y) mod 2^256  */
  bn.sub    w2, w31, w2

  /* Store result in dmem[m0inv]. */
  li        x9, 2
  la        x26, m0inv
  bn.sid    x9, 0(x26)

  ret

/* Input buffer for the modulus. */
.section .bss.in_mod
.weak in_mod
in_mod:
  .zero 384

/* Output buffer for the Montgomery constant. */
.section .bss.m0inv
.weak m0inv
m0inv:
  .zero 32
