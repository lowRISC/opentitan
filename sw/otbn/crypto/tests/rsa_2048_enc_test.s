/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


.section .text.start

/**
 * Standalone RSA-2048 modexp with e=65537 (encryption/verification).
 */
main:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Load number of limbs. */
  li    x30, 8

  /* Load pointers to modulus and Montgomery constant buffers. */
  la    x16, rsa_n
  la    x17, RR

  /* Compute Montgomery constants. */
  jal      x1, modload

  /* Run exponentiation.
       dmem[work_buf] = dmem[inout]^dmem[d] mod dmem[n] */
  la       x14, inout
  la       x2, work_buf
  jal      x1, modexp_65537

  /* copy all limbs of result to wide reg file */
  la       x21, work_buf
  li       x8, 0
  loop     x30, 2
    bn.lid   x8, 0(x21++)
    addi     x8, x8, 1

  ecall
