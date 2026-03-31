/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that the z and h public key polynomials can correctly be decoded. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _sig_decode_encoded_h
  la x3, _sig_decode_decoded_h
  la x4, _sig_decode_encoded_z
  la x5, _sig_decode_decoded_z
  jal x1, sig_decode

  ecall

.data
.balign 32

_sig_decode_encoded_z:
.zero 4480
_sig_decode_decoded_z:
.zero 7168

_sig_decode_encoded_h:
.zero 83
.zero 13 /* Padding */
_sig_decode_decoded_h:
.zero 332
.zero 20 /* Padding */

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
