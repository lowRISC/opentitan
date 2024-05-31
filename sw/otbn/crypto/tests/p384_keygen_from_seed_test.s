/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 key generation from seed
 *
 * Performs generation of a P-384 random secret key using a
 * random seed as input.
 *
 * This test does not test if the randomness of the generated values is
 * properly distributed or if the entropy is large enough etc.
 * It only checks if the key is generated correctly.
 *
 * Actual randomness testing has to be done vial statistical analysis
 * of generated values, but this is not possible for simulator based
 * automated testing.
 */

.section .text.start

p384_keygen_from_seed_test:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Load the curve order n.
     [w13,w12] <= dmem[p384_n] = n */
  li        x2, 12
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* Compute Solinas constant k for modulus n (we know it is only 191 bits, so
     no need to compute the high part):
     w14 <= 2^256 - n[255:0] = (2^384 - n) mod (2^256) = 2^384 - n */
  bn.sub    w14, w31, w12

  /* Obtain 1024 bits of randomness from URND. */
  bn.wsrr   w20, URND
  bn.wsrr   w21, URND
  bn.wsrr   w10, URND
  bn.wsrr   w11, URND

  /* Reduce to 384 bits of randomness per share.
       [w21, w20] <= s0 mod 2^384
       [w11, w10] <= s1 mod 2^384 */
  bn.rshi   w21, w21, w31 >> 128
  bn.rshi   w21, w31, w21 >> 128
  bn.rshi   w11, w11, w31 >> 128
  bn.rshi   w11, w31, w11 >> 128

  /* Calculate seed = s0 ^ s1
     [w9,w8] <= [w21,w20] ^ [w11,w10] */
  bn.xor    w8, w20, w10
  bn.xor    w9, w21, w11

  /* Generate key shares
     dmem[d0] <= d0
     dmem[di] <= d1 */
  jal       x1, p384_key_from_seed

  /* Calculate d = seed mod n
     [w1,w0] <= [w19,w18] mod [w13,w12] */
  bn.mov    w18, w8
  bn.mov    w19, w9
  bn.mov    w20, w31
  jal       x1, p384_reduce_n
  bn.mov    w0, w16
  bn.mov    w1, w17

  /* Load secred key shares from DMEM */
  /* [w5,w4] <= d0 */
  la        x4, d0
  li        x2, 4
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* [w7,w6] <= d1 */
  la        x4, d1
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* Calculate d' = d0 + d1 mod n
     [w17,w16] <= [w5,w4] + [w7,w6] mod [w13,w12] */
  bn.add    w18, w4, w6
  bn.addc   w19, w5, w7
  bn.mov    w20, w31
  jal       x1, p384_reduce_n

  /* Compare if d == d' */
  bn.sub    w0, w0, w16
  bn.subb   w1, w1, w17

  ecall

.section .data

.balign 32

/* 1st private key share d0 (448-bit) */
.globl d0
d0:
  .zero 64

/* 2nd private key share d1 (448-bit) */
.globl d1
d1:
  .zero 64
