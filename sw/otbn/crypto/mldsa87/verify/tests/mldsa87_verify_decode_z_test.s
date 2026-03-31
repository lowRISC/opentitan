/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

main:
  /* Setup stack pointer and all-zero WDR. */
  la x31, _stack
  bn.xor w31, w31, w31

  /* Load the parameters into the MOD WSR. */
  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _decode_z_enc
  la x3, _decode_z_dec
  jal x1, decode_z

  ecall

.data
.balign 32

_decode_z_enc:
.zero 640
_decode_z_dec:
.zero 1024

/*
 * q  = 8380417 = 2^23 - 2^13 + 1 (ML-DSA modulus)
 * mu = -q^-1 mod R (Montgomery constant)
 * f  = 256^-1 * R mod q (INTT divisor in Montgomery domain)
 */
_params:
.word 0x007fe001 /* q */
.word 0xfc7fdfff /* mu */
.word 0x00003ffe /* f */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

_stack:
.zero 4
