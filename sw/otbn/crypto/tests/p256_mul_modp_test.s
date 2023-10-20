/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-256 field multiplication.
 */

.section .text.start
start:
  /* Initialize all-zero register. */
  bn.xor    w31, w31, w31

  /* Load the modulus, p.
     MOD <= w29 <= dmem[p256_p] = p */
  li        x2, 29
  la        x3, p256_p
  bn.lid    x2, 0(x3)
  bn.wsrw   MOD, w29

  /* Compute the constant r256 for reduction modulo p.
       w28 <= 2^256 - p = r256 */
  bn.sub   w28, w31, w29

  /* Load the constant for reduction modulo p.
     w29 <= dmem[p256_r448] = r448 */
  li        x2, 29
  la        x3, p256_r448
  bn.lid    x2, 0(x3)

  /* Load the operands.
       w24 <= dmem[value_a] = a
       w25 <= dmem[value_b] = b */
  li        x2, 24
  la        x3, value_a
  bn.lid    x2++, 0(x3)
  la        x3, value_b
  bn.lid    x2, 0(x3)

  /* Run modular multiplication.
       w19 <= (w24 * w25) mod p */
  jal       x1, mul_modp

  ecall

.data

/* First operand, a.
   = 0xa8da539ffce03337030a5a44bcd3266608a32b364bb3295cace17a9da3175abc */
value_a:
.word 0xa3175abc
.word 0xace17a9d
.word 0x4bb3295c
.word 0x08a32b36
.word 0xbcd32666
.word 0x030a5a44
.word 0xfce03337
.word 0xa8da539f

/* Second operand, b.
   = 0x72c7c6bec94cf13ab2a1c47c60cb522e04a0e4330df8714c96a2db313c873171 */
value_b:
.word 0x3c873171
.word 0x96a2db31
.word 0x0df8714c
.word 0x04a0e433
.word 0x60cb522e
.word 0xb2a1c47c
.word 0xc94cf13a
.word 0x72c7c6be
