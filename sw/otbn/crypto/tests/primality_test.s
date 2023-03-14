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
0x9ac5b6d69aa1d91c418d9bf315ba72595488aabddbd435dafe630ba818e3d4ef03ab9bf93147a781cc45f6219f8bc92fc500c92dc8539832055036f6537320a1
*/
.balign 32
input:
.word 0x537320a1
.word 0x055036f6
.word 0xc8539832
.word 0xc500c92d
.word 0x9f8bc92f
.word 0xcc45f621
.word 0x3147a781
.word 0x03ab9bf9
.word 0x18e3d4ef
.word 0xfe630ba8
.word 0xdbd435da
.word 0x5488aabd
.word 0x15ba7259
.word 0x418d9bf3
.word 0x9aa1d91c
.word 0x9ac5b6d6

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
