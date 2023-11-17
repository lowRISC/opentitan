/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   P-384 specific routines for ECC modular inverse computation.
 */

 .section .text

/**
 * Variable-time modular multiplicative inverse computation
 *
 * returns x_inv = x^-1 mod m
 *
 * This routine computes the modular multiplicative inverse for any x < m in
 * the finite field GF(m) where m is prime.
 *
 * For inverse computation, Fermat's little theorem is used, i.e.
 * we compute x^-1 = x^(m-2) mod m.
 * For exponentiation we use a standard, variable-time (!) square and multiply
 * algorithm.
 *
 * This routine is mainly intended to be used for inversion of scalars in
 * context of the P-384 curve. In theory, it can be used with any 384-bit
 * modulus m with a corresponding 385-bit Barrett constant u,
 * where u[383:192] = 0.
 *
 * Note: When used for P-384 scalar inversion, the routine will need 672 calls
 * to the multiplication routine. By using an adder chain this could be reduced
 * to ~433 multiplications, however, at the cost of a significant code size
 * increase.
 *
 * Note: This routine runs in variable-time w.r.t. the modulus. It should only
 * be used with a non-secret modulus.
 *
 * @param[in]  [w13, w12]: m, 384 bit modulus
 * @param[in]  w14: k, Solinas constant (2^384 - m) (max. length 191 bits).
 * @param[in]  [w30, w29]: x, 384 bit operand
 * @param[in]  w31, all-zero
 * @param[out] [w17, w16]: x_inv, modular multiplicative inverse
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: x2, w2, w3, w10, w11, w16 to w24
 * clobbered flag groups: FG0
 */
 .globl mod_inv_n_p384
mod_inv_n_p384:

  /* subtract 2 from modulus for Fermat's little theorem
     [w3,w2] <= m - 2 = [w13,w12]-2 (left aligned) */
  bn.subi   w2, w12, 2
  bn.subb   w3, w13, w31
  bn.rshi   w3, w3, w2 >> 128
  bn.rshi   w2, w2, w31 >> 128

  /* init square and multiply: [w17,w16] = 1 */
  bn.addi   w16, w31, 1
  bn.mov    w17, w31

  /* square and multiply loop */
  loopi     384, 12

    /* square: [w17,w16] <= [w17, w16]*[w11,w10] mod [w13, w12] */
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_n

    /* shift MSB into carry flag
       [w3,w2] = 2*[w3,w2] = [w3,w2] << 1 */
    bn.add    w2, w2, w2
    bn.addc   w3, w3, w3

    /* skip multiplication if C flag not set */
    csrrs     x2, 0x7c0, x0
    andi      x2, x2, 1
    beq       x2, x0, nomul

    /* multiply: [w17,w16] <= [w17, w16]*[w30,w29] mod [w13, w12] */
    bn.mov    w10, w29
    bn.mov    w11, w30
    jal       x1, p384_mulmod_n

    nomul:
    nop

  ret
