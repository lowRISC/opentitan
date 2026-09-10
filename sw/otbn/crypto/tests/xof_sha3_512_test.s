/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that the SHA3-512 interface can correctly absorb and squeeze data. */

.section .text.start

main:
  bn.xor w31, w31, w31

  /*
   * Test case 1: Absorb 3 bytes, squeeze 64 bytes (2 WDR words).
   */
  jal x1, xof_sha3_512_init

  addi x20, x0, 3
  la x21, _xof_msg_3b
  addi x22, x0, 0
  jal x1, xof_absorb
  jal x1, xof_process

  jal x1, xof_squeeze32
  bn.xor w1, w29, w30

  jal x1, xof_squeeze32
  bn.xor w2, w29, w30

  jal x1, xof_finish

  /*
   * Test case 2: Absorb 32 bytes, squeeze 64 bytes (2 WDR words).
   */
  jal x1, xof_sha3_512_init

  addi x20, x0, 32
  la x21, _xof_msg_32b
  addi x22, x0, 0
  jal x1, xof_absorb
  jal x1, xof_process

  jal x1, xof_squeeze32
  bn.xor w3, w29, w30

  jal x1, xof_squeeze32
  bn.xor w4, w29, w30

  jal x1, xof_finish

  /*
   * Test case 3: Absorb 48 bytes, squeeze 64 bytes (2 WDR words).
   */
  jal x1, xof_sha3_512_init

  addi x20, x0, 48
  la x21, _xof_msg_48b
  addi x22, x0, 0
  jal x1, xof_absorb
  jal x1, xof_process

  jal x1, xof_squeeze32
  bn.xor w5, w29, w30

  jal x1, xof_squeeze32
  bn.xor w6, w29, w30

  jal x1, xof_finish

  /*
   * Test case 4: Absorb 128 bytes, squeeze 64 bytes (2 WDR words).
   */
  jal x1, xof_sha3_512_init

  addi x20, x0, 128
  la x21, _xof_msg_128b
  addi x22, x0, 0
  jal x1, xof_absorb
  jal x1, xof_process

  jal x1, xof_squeeze32
  bn.xor w7, w29, w30

  jal x1, xof_squeeze32
  bn.xor w8, w29, w30

  jal x1, xof_finish

  ecall

.data
.balign 32

_xof_msg_3b:
.zero 3
.zero 29 /* Padding */
_xof_msg_32b:
.zero 32
_xof_msg_48b:
.zero 48
.zero 16 /* Padding */
_xof_msg_128b:
.zero 128

_stack:
.zero 256
