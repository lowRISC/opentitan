/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for Miller-Rabin primality test.
 *
 * The test input is composite, so we expect the primality test to fail. Uses
 * n=4 limbs (i.e. a 1024-bit prime candidate, as would be used in RSA-2048).
 */

.section .text.start

main:
  /* Initialize all-zero register. */
  bn.xor    w31, w31, w31

  /* Number of limbs (n) and related constant.
       x30 <= n
       x31 <= n - 1 */
  li        x30, 4
  li        x31, 3

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

  /* Set number of Miller-Rabin rounds (see FIPS 186-5, table B.1). */
  li        x10, 4

  /* Call primality test.
       w21 <= all 1s if dmem[input] is probably prime, otherwise 0 */
  jal        x1, miller_rabin

  ecall

.data

/* Candidate prime (Wycheproof test #39) =
0xf67307e54779cfe9120bf862afc5466c5d6d0783d12df5215c0c981c51e4bfc098e9afd574f51b18c820259b692ec0bf7c9d6e56e9bb99fbd3b7ecc4082146a9d7a5b7bc6519d476c4a9975d9c3e3b12bee45b7accb07a6a68ea583ac2523ef32ee6d01bc766b59c43031f9c6980c9b4317da6825be9f7c5db03283d04c13323

Note: this prime is a worst-case test for Miller-Rabin, since it has a high
probability of producing false positives if the number of rounds is too low.
*/
.balign 32
input:
.word 0x04c13323
.word 0xdb03283d
.word 0x5be9f7c5
.word 0x317da682
.word 0x6980c9b4
.word 0x43031f9c
.word 0xc766b59c
.word 0x2ee6d01b
.word 0xc2523ef3
.word 0x68ea583a
.word 0xccb07a6a
.word 0xbee45b7a
.word 0x9c3e3b12
.word 0xc4a9975d
.word 0x6519d476
.word 0xd7a5b7bc
.word 0x082146a9
.word 0xd3b7ecc4
.word 0xe9bb99fb
.word 0x7c9d6e56
.word 0x692ec0bf
.word 0xc820259b
.word 0x74f51b18
.word 0x98e9afd5
.word 0x51e4bfc0
.word 0x5c0c981c
.word 0xd12df521
.word 0x5d6d0783
.word 0xafc5466c
.word 0x120bf862
.word 0x4779cfe9
.word 0xf67307e5

.section .scratchpad

/* Space for Montgomery constant m0' (256 bits). */
.balign 32
mont_m0inv:
.zero 32

/* Space for Montgomery constant RR (1024 bits). */
.balign 32
mont_rr:
.zero 128

/* Temporary working buffer 1 (1024 bits). */
.balign 32
tmp1:
.zero 128

/* Temporary working buffer 2 (1024 bits). */
.balign 32
tmp2:
.zero 128
