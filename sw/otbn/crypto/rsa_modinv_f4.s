/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.text
.globl modinv_f4

/**
 * Calculate e^-1 mod f, for e == 2^16 + 1 and an n-limbed even integer f.
 *
 * This routine implements the modular inversion of F4 by the means of the
 * Arazi's method such that
 *
 * e^-1 = (1 + f * (-f^(e - 2) mod e)) / e
 *
 * This routine is used to calculate the secret RSA key d = e^-1 mod f, where
 * f = lcm(p - 1, q- 1) is always an even integer.
 *
 * @param[in] x24: f, DMEM pointer to the first limb of f.
 * @param[in] x25: e^-1, DMEM pointer to the first limb of the result.
 * @param[in] x26: DMEM pointer to a temporary slot (>= 32 bytes).
 * @param[in] x27: n, number of limbs of f.
 * @param[in] w31: all-zero.
 */
modinv_f4:
  /* Calculate f mod e. */
  addi x16, x24, 0
  addi x31, x27, 0
  jal x1, mod_f4

  /* Calculate -f mod e. */
  bn.addi w0, w31, 1
  bn.rshi w0, w0, w31 >> 240
  bn.addi w0, w0, 1
  bn.sub w0, w0, w22

  /*
   * Calculate the modular exponentiation -f^(e - 2) mod e, where
   * e - 2 = 0xffff.
   */

  bn.addi w1, w31, 1

  loopi 16, 6
    bn.mulqacc.wo.z w23, w0.0, w1.0, 0
    jal x1, mod_f4_35
    bn.mov w1, w22

    bn.mulqacc.wo.z w23, w0.0, w0.0, 0
    jal x1, mod_f4_35
    bn.mov w0, w22
    /* End of loop */

  /* Store the result at the temporary slot. */
  bn.mov w0, w1
  bn.sid x0, 0(x26)

  /* Calculate f * (-f^(e - 2) mod e), where f is an n-limbed even integer. */
  addi x10, x24, 0
  addi x11, x26, 0
  addi x12, x25, 0
  addi x30, x27, 0
  addi x31, x0, 1
  jal x1, bignum_mul

  /* Calculate 1 + f * (-f^(e - 2) mod e). f * (-f^(e - 2) mod e) is even. */
  bn.lid x0, 0(x25)
  bn.addi w0, w0, 1
  bn.sid x0, 0(x25)

  /* Divide 1 + f * (-f^(e - 2) mod e) by e. */

  /* e */
  bn.addi w20, w31, 1
  bn.rshi w20, w20, w31 >> 240
  bn.addi w20, w20, 1

  /* e^-1 mod 2^256 = 0xffff0000ffff0000...ffff0001. */
  bn.subi w1, w31, 1
  loopi 16, 2
    bn.rshi w21, w31, w21 >> 16
    bn.rshi w21, w1, w21 >> 16
  bn.addi w21, w21, 1

  addi x16, x25, 0
  addi x31, x27, 1
  jal x1, div_word

  ret
