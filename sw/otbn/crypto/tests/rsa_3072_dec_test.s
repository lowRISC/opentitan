/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


.section .text.start

/**
 * Standalone RSA-3072 modexp with secret exponent (decryption/signing).
 */
main:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Enable message blinding. */
  li x29, 1

  /* Load number of limbs. */
  li    x30, 12

  /* Load pointers to modulus and Montgomery constant buffers. */
  la    x16, rsa_n
  la    x17, RR

  /* Compute Montgomery constants. */
  jal      x1, modload

  /* Run exponentiation.
       dmem[inout] = dmem[inout]^dmem[d] mod dmem[n] */
  jal      x1, modexp

  /* copy all limbs of result to wide reg file */
  la       x21, r0
  li       x8, 0
  loop     x30, 2
    bn.lid   x8, 0(x21++)
    addi     x8, x8, 1

  ecall
