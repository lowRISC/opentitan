/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


.section .text.start

/**
 * Standalone RSA-2048 modexp with secret exponent (decryption/signing).
 */
main:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Load number of limbs. */
  li    x30, 8

  /* Load pointers to modulus and Montgomery constant buffers. */
  la    x16, n
  la    x17, RR

  /* Compute Montgomery constants. */
  jal      x1, modload

  /* Run exponentiation.
       dmem[work_buf] = dmem[inout]^dmem[d] mod dmem[n] */
  la       x14, inout
  la       x15, d0
  la       x2, work_buf
  jal      x1, modexp

  /* copy all limbs of result to wide reg file */
  la       x21, work_buf
  li       x8, 0
  loop     x30, 2
    bn.lid   x8, 0(x21++)
    addi     x8, x8, 1

  ecall
