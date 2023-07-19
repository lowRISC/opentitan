/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 ECDSA signature generation
 *
 * Computes P-384 ECDSA signature for message, nonce and private key
 * contained in the .data section.
 *
 * See comment at the end of the file for expected values of signature.
 */

.section .text.start

p384_mulmod448x128_test:

  /* init all-zero reg */
  bn.xor    w31, w31, w31

  /* load multiplication input into WDRs
     [w11,w10] <= a
     w16 <= b */
  li        x2, 10
  la        x3, a
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)
  li        x2, 16
  la        x3, b
  bn.lid    x2, 0(x3)

  /* load domain parameter n (order of base point)
     [w13, w12] <= n = dmem[dptr_n] */
  li        x2, 12
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* Compute Solinas constant k for modulus n (we know it is only 191 bits, so
     no need to compute the high part):
     w14 <= 2^256 - n[255:0] = (2^384 - n) mod (2^256) = 2^384 - n */
  bn.sub    w14, w31, w12

  /* Compute a * b mod n
     [w17,w16] <= [w11,w10] * w16 mod [w13,w12] = a * b mod n */
  jal       x1, p384_mulmod448x128_n

  /* move result to different WDRs for comparison */
  bn.mov    w0, w16
  bn.mov    w1, w17

  ecall


.data

a:
  .word 0x5c832a51
  .word 0x3eb17c27
  .word 0x9a0c1b76
  .word 0x6e001281
  .word 0x4de8344e
  .word 0x5b7d3b0f
  .word 0x96d2f9e0
  .word 0x1e9d19e7
  .word 0x16f5c1ee
  .word 0x800a4c94
  .word 0xe14cd8df
  .word 0xadb9ce1b
  .word 0x8677a5f2
  .word 0x32f9e2b0
  .zero 8

b:
  .word 0x5c832a51
  .word 0x3eb17c27
  .word 0x9a0c1b76
  .word 0x6e001281
  .zero 48
