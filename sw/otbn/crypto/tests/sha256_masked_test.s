/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start
main:
  /* Set the number of message chunks (in blocks of 512 bits) */
  li      x30, 2

  /* Load pointers to Share 0 and Share 1 of the padded message */
  la      x10, msg_s0
  la      x11, msg_s1

  /* Run the SHA-256 masked process */
  jal     x1, sha256_masked

  /* Load the final state into registers for the test environment to check */
  la      x2, state_s0
  bn.lid  x0, 0(x2)
  la      x2, state_s1
  li x3, 1
  bn.lid x3, 0(x2)

  /* The unmasked result must be equal to standard SHA-256 */
  bn.xor  w2, w0, w1

  ecall

.data

/* The NIST Two Block Message, split into two arbitrary boolean shares */
.balign 32
msg_s0:
.word 0x64636261 ^ 0x11111111
.word 0x65646362 ^ 0x22222222
.word 0x66656463 ^ 0x33333333
.word 0x67666564 ^ 0x44444444
.word 0x68676665 ^ 0x55555555
.word 0x69686766 ^ 0x66666666
.word 0x6A696867 ^ 0x77777777
.word 0x6B6A6968 ^ 0x88888888
.word 0x6C6B6A69 ^ 0x11111111
.word 0x6D6C6B6A ^ 0x22222222
.word 0x6E6D6C6B ^ 0x33333333
.word 0x6F6E6D6C ^ 0x44444444
.word 0x706F6E6D ^ 0x55555555
.word 0x71706F6E ^ 0x66666666
.word 0x00000080 ^ 0x77777777
.word 0x00000000 ^ 0x88888888
.word 0x00000000 ^ 0x11111111
.word 0x00000000 ^ 0x22222222
.word 0x00000000 ^ 0x33333333
.word 0x00000000 ^ 0x44444444
.word 0x00000000 ^ 0x55555555
.word 0x00000000 ^ 0x66666666
.word 0x00000000 ^ 0x77777777
.word 0x00000000 ^ 0x88888888
.word 0x00000000 ^ 0x11111111
.word 0x00000000 ^ 0x22222222
.word 0x00000000 ^ 0x33333333
.word 0x00000000 ^ 0x44444444
.word 0x00000000 ^ 0x55555555
.word 0x00000000 ^ 0x66666666
.word 0x00000000 ^ 0x77777777
.word 0xC0010000 ^ 0x88888888

.balign 32
msg_s1:
.word 0x11111111, 0x22222222, 0x33333333, 0x44444444
.word 0x55555555, 0x66666666, 0x77777777, 0x88888888
.word 0x11111111, 0x22222222, 0x33333333, 0x44444444
.word 0x55555555, 0x66666666, 0x77777777, 0x88888888
.word 0x11111111, 0x22222222, 0x33333333, 0x44444444
.word 0x55555555, 0x66666666, 0x77777777, 0x88888888
.word 0x11111111, 0x22222222, 0x33333333, 0x44444444
.word 0x55555555, 0x66666666, 0x77777777, 0x88888888

/* Pre-shared initial hash state (Standard IV constants masked with ABCDEF01) */
.balign 32
.globl state_s0
state_s0:
.word 0x5be0cd19 ^ 0xABCDEF01
.word 0x1f83d9ab ^ 0xABCDEF01
.word 0x9b05688c ^ 0xABCDEF01
.word 0x510e527f ^ 0xABCDEF01
.word 0xa54ff53a ^ 0xABCDEF01
.word 0x3c6ef372 ^ 0xABCDEF01
.word 0xbb67ae85 ^ 0xABCDEF01
.word 0x6a09e667 ^ 0xABCDEF01

.balign 32
.globl state_s1
state_s1:
.word 0xABCDEF01, 0xABCDEF01, 0xABCDEF01, 0xABCDEF01
.word 0xABCDEF01, 0xABCDEF01, 0xABCDEF01, 0xABCDEF01
