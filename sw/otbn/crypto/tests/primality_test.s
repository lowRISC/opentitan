/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for Miller-Rabin primality test.
 *
 * The prime candidate in this case is a true prime, so we expect the primality
 * test to succeed. Uses n=2 limbs (i.e. a 512-bit prime candidate, as would be
 * used in RSA-1024).
 */

.section .text.start

main:
  /* Initialize all-zero register. */
  bn.xor    w31, w31, w31

  /* Number of limbs (n) and related constant.
       x30 <= n
       x31 <= n - 1 */
  li        x30, 2
  li        x31, 1

  /* Compute Montgomery constants for the candidate prime.
       dmem[mont_m0inv] <= (- dmem[input]) mod 2^256
       dmem[mont_rr] <= (2^1024) mod dmem[input] */
  la         x16, input
  la         x17, mont_m0inv
  la         x18, mont_rr
  jal        x1, modload


  /* Load pointers to temporary work buffers. */
  la         x14, tmp1
  la         x15, tmp2

  /* Set number of Miller-Rabin rounds. The prime should survive any number of
     rounds, but we set a roughly realistic number. */
  li        x10, 4

  /* Call primality test.
       w21 <= all 1s if dmem[input] is probably prime, otherwise 0 */
  jal        x1, miller_rabin

  /* Load Mont constants.
       w0 <= m0_inv
       w1, w2 <= rr */
  la         x17, mont_m0inv
  la         x18, mont_rr
  li         x2, 0
  bn.lid     x2++, 0(x17)
  bn.lid     x2++, 0(x18)
  bn.lid     x2++, 32(x18)

  ecall

.data

/* Candidate prime (randomly generated using pycryptodome) =
0x83f4fb7ca746b70dd7e37ce93847ed7995ccf101bb7a9c628ebcffeeaa0114efd346ddfb53c1d31d51ab13bbcb0b2346d6689cd78210bfe05f458233d8e58e1b
*/
.balign 32
input:
.word 0xd8e58e1b
.word 0x5f458233
.word 0x8210bfe0
.word 0xd6689cd7
.word 0xcb0b2346
.word 0x51ab13bb
.word 0x53c1d31d
.word 0xd346ddfb
.word 0xaa0114ef
.word 0x8ebcffee
.word 0xbb7a9c62
.word 0x95ccf101
.word 0x3847ed79
.word 0xd7e37ce9
.word 0xa746b70d
.word 0x83f4fb7c

.section .scratchpad

/* Space for Montgomery constant m0' (256 bits). */
.balign 32
mont_m0inv:
.zero 32

/* Space for Montgomery constant RR (512 bits). */
.balign 32
mont_rr:
.zero 64

/* Temporary working buffer 1 (512 bits). */
.balign 32
tmp1:
.zero 64

/* Temporary working buffer 2 (512 bits). */
.balign 32
tmp2:
.zero 64
