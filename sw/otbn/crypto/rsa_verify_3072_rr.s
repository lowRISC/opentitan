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
 *   rr:    INPUT
 *             384 bytes
 *             The Montgomery transformation constant R^2 = (2^3072)^2 mod N
 */

.text

/**
 * Subtracts the modulus M from A.
 *
 * Flags: After this subroutine, the C flag is set to 1 if the subtraction
 * underflowed.
 *
 * This routine runs in variable time.
 * @param[in]  x16: dmem pointer to first limb of modulus M
 * @param[in]  [w4:w15]: operand A
 * @param[in]  w31: all-zero
 * @param[out] [w16:w27]: result
 *
 * clobbered registers: x8 to x12, w2, w3, w16 to w27
 * clobbered Flag Groups: FG0
 */
subtract_modulus_var:

  /* Prepare temporary registers. */
  li        x8, 4
  li        x9, 2
  li        x10, 3
  li        x11, 16

  /* Copy pointer to modulus. */
  addi      x12, x16, 0

  /* Clear flags. */
  bn.add    w31, w31, w31

  /* Subtract M from A. */
  loopi     12, 4
    /* w2 <= A[i] */
    bn.movr   x9, x8++
    /* w3 <= M[i] */
    bn.lid    x10, 0(x12++)
    /* w2 <= w2 - w3 */
    bn.subb   w2, w2, w3
    /* out[i] <= w2 */
    bn.movr   x11++, x9

  ret

/**
 * Doubles a number and reduces modulo M in-place.
 *
 *   Returns: C = (A + A) mod M
 *
 * Requires that A < M < 2^3072. Writes output to the A buffer in DMEM. This
 * routine runs in variable time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x16: dmem pointer to first limb of modulus M
 * @param[in]  [w4:w15]: operand A
 * @param[in]  w31: all-zero
 * @param[out] [w4:w15]: result C
 *
 * clobbered registers: x2, x3, x7 to x12, w2 to w27
 * clobbered Flag Groups: FG0
 */
double_mod_var:
  /* Save copy of pointer to modulus. */
  addi      x12, x16, 0

  /* Clear flags. */
  bn.add    w31, w31, w31

  /* Compute aa=(A + A).
       [w4:w15] <= (A+A) mod 2^3072 = aa[0:3071]*/
  li        x9, 2
  li        x10, 4
  loopi     12, 3
    /* w2 <= a[i] */
    bn.movr   x9, x10
    /* w2 <= w2 + w2 */
    bn.addc   w2, w2, w2
    /* aa[i] <= w2 */
    bn.movr   x10++, x9

  /* Extract final carry bit from flags register.
       x2 <= aa[3072] */
  csrrs     x2, FG0, x0
  andi      x2, x2, 1

  jal       x1, subtract_modulus_var

  /* Extract final borrow bit from flags register. */
  csrrs     x3, FG0, x0
  andi      x3, x3, 1

  /**
   * Select either aa or aa' based on carry/borrow bits.
   *
   * If aa < M, it follows that the carry bit aa[3072] = 0 (since M < 2^3072).
   * It also follows that the borrow from subtracting M must be 1. In this
   * case, select aa; otherwise, select aa-M.
   */

  /* x2 <= (!x2) & x3 */
  xori      x2, x2, 1
  and       x2, x2, x3

  /* Select aa if x2 = 0, otherwise aa-M. */
  bne       x2, x0, sel_aa

  /* Copy subtraction result to w4:w15. */
  li        x8, 4
  li        x11, 16
  loopi     12, 2
    bn.movr   x8, x11++
    addi      x8, x8, 1

sel_aa:

  ret

/**
 * Computes the R^2 Montgomery constant and stores it in DMEM.
 *
 *   Returns RR = (2^3072)^2 mod M
 *
 * A note on bounds: This computation assumes that 2^3071 <= M < 2^3072. This
 * agrees with FIPS 186-4 section B.3.1 (page 53), which states that the prime
 * factors of the RSA modulus must be at least sqrt(2)*2^(nlen/2-1) (where nlen
 * is the key length, 3072 in this case).
 *
 * The result is stored in dmem[rr]. This routine runs in variable time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  dmem[in_mod] pointer to first limb of modulus M in dmem
 * @param[in]  dmem[m0inv]  Montgomery constant (-(M^-1) mod 2^256)
 * @param[out] dmem[rr]     Montgomery constant (R^2) mod M
 *
 * clobbered registers: x0 to x3, x6 to x13, x16, x17, x19 to x22, x24,
 *                      w2 to w31
 * clobbered Flag Groups: FG0, FG1
 */
 .globl compute_rr
compute_rr:
  /* Prepare all-zero register. */
  bn.xor    w31, w31, w31

  /* Set pointers to DMEM buffers. */
  la        x16, in_mod
  la        x17, m0inv
  la        x24, rr

  /* Zero [w4:w15]. */
  li        x9, 4
  li        x10, 31
  loopi     12, 1
    bn.movr   x9++, x10

  /* w16 <= 1 */
  bn.addi   w16, w31, 1

  /* [w4:w15] <= [w4:w16] >> 1 = 2^3701 */
  bn.rshi   w15, w16, w15 >> 1

  /* Compute T = (2^96 * R) mod M = 2^96 (montgomery form).
     T = [w4:w15] = (2^97 * 2^3071) mod M = (2^96 * R) mod M */
  loopi     97,2
    jal x1, double_mod_var
    nop

  /* Store T in output buffer (in preparation for montmul).
     dmem[rr] <= [w4:w15] = T */
  li        x8, 4
  addi      x21, x24, 0
  loopi     12, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  /* Prepare pointers to temp regs for montmul. */
  li        x9, 3
  li        x10, 4
  li        x11, 2

  /* Prepare a pointer to the w4 register for storing the result. */
  li        x8, 4

  /* Five montgomery squares to compute RR = (T^(2^5) * R) mod M. */
  loopi     5,9
    /* [w4:w15] <= montmul(dmem[rr], dmem[rr]) */
    addi      x19, x24, 0
    addi      x20, x24, 0
    jal       x1, montmul
    /* Store result: dmem[rr] <= [w4:w15] */
    addi      x21, x24, 0
    addi      x22, x8, 0
    loopi     12, 2
      bn.sid    x22, 0(x21++)
      addi      x22, x22, 1
    nop

  ret

/* Input buffer for the Montgomery constant m0_inv. */
.section .data.m0inv
.weak m0inv
m0inv:
  .zero 32

/* Input buffer for the modulus. */
.section .bss.in_mod
.weak in_mod
in_mod:
  .zero 384

/* Output buffer for the Montgomery transformation constant R^2. */
.section .bss.rr
.weak rr
rr:
  .zero 384
