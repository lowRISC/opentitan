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
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 1

  jal       x1, subtract_modulus_var

  /* Extract final borrow bit from flags register. */
  csrrs     x3, 0x7c0, x0
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
 * This implementation is based on section 2.3 of "Montgomery Arithmetic from a
 * Software Perspective" (https://eprint.iacr.org/2017/1057). For the purposes
 * of RSA 3072, the parameters w and n from the paper are fixed (w=256, n=12).
 *
 * A note on bounds: the algorithm from the paper states an assumption that
 * 2^wn-1 <= M < 2^wn (in our case, 2^3071 <= M < 2^3072). We make that
 * assumption here too, because it agrees with FIPS 186-4 section B.3.1 (page
 * 53), which states that the prime factors of the RSA modulus must be at least
 * sqrt(2)*2^(nlen/2-1) (where nlen is the key length, 3072 in this case).
 *
 * The result is stored in dmem[rr]. This routine runs in variable time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  dmem[in_mod] pointer to first limb of modulus M in dmem
 *
 * clobbered registers: x9, x10, x16, w4 to w16, w31
 * clobbered Flag Groups: FG0
 */
 .globl compute_rr
compute_rr:
  /* Prepare all-zero register. */
  bn.xor    w31, w31, w31

  /* Set pointer to modulus. */
  la        x16, in_mod

  /* Zero [w4:w15]. */
  li        x9, 4
  li        x10, 31
  loopi     12, 1
    bn.movr   x9++, x10

  /* w16 <= 1 */
  bn.addi   w16, w31, 1

  /* Initialize c0.
     c0 = [w4:w15] <= [w4:w16] >> 1 = 2^3701 */
  bn.rshi   w15, w16, w15 >> 1

  /* One modular doubling to get c1 \equiv 2^3072 mod M.
     c1 = [w4:w15] <= ([w4:w15] * 2) mod M = (2^3072) mod M */
  jal     x1, double_mod_var

  /* Compute (2^3072)^2 mod M by performing 3072 modular doublings. */
  li      x9, 3072
  loop     x9, 4
    jal     x1, double_mod_var
    /* Nop because loop can't end on a jump instruction. */
    nop

  /* Store result in dmem[rr]. */
  li        x9, 4
  la        x10, rr
  loopi     12, 2
    bn.sid    x9, 0(x10++)
    addi      x9, x9, 1

  ret

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
