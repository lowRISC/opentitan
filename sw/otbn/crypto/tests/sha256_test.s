/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


/**
 * Standalone tests for SHA-512 hash computation.
 *
 * Based on NIST example (two-block message, second example):
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf
 *
 * Input message: "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
 */

.section .text.start
main:
  /* Set the number of message chunks.
       x30 <= 1 */
  li      x30, 2

  /* Run the sha256 process and update the state.
       dmem[state] = sha256(dmem[state], dmem[msg..msg+64] */
  la      x10, msg
  jal     x1, sha256

  /* Load the final state into a register for the test to check.
       w0 <= dmem[state] */
  la      x2, state
  bn.lid  x0, 0(x2)

  ecall

.data

/* Message (already padded). */
.balign 32
msg:
.word 0x61626364
.word 0x62636465
.word 0x63646566
.word 0x64656667
.word 0x65666768
.word 0x66676869
.word 0x6768696A
.word 0x68696A6B
.word 0x696A6B6C
.word 0x6A6B6C6D
.word 0x6B6C6D6E
.word 0x6C6D6E6F
.word 0x6D6E6F70
.word 0x6E6F7071
.word 0x80000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x000001C0

/**
 * Starting hash state (initial values for SHA-256).
 *
 * Represented in big-endian order to match FIPS 180-4, so the first word in
 * this sequence is H[7] and the last is H[0].
 */
.balign 32
.globl state
state:
.word 0x5be0cd19
.word 0x1f83d9ab
.word 0x9b05688c
.word 0x510e527f
.word 0xa54ff53a
.word 0x3c6ef372
.word 0xbb67ae85
.word 0x6a09e667
