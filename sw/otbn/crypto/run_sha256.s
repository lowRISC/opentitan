/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start
main:
  /* Load the number of message chunks.
       x30 <= dmem[num_msg_chunks] */
  la     x2, num_msg_chunks
  lw     x30, 0(x2)

  /* Run the sha256 process and update the state.
       dmem[state] = sha256(dmem[state], dmem[msg..msg+x30*64] */
  la     x10, msg
  jal    x1, sha256

  ecall

.bss

/* Length of message (in chunks). */
.balign 4
.globl num_msg_chunks
num_msg_chunks:
.zero 4

/**
 * Input message (must already be padded).
 *
 * The message size is limited by available DMEM space. Out of a bus-accessible
 * 3kiB, SHA-256 uses:
 *  - 64*4 = 256 bytes for round constants
 *  - 32 bytes for hash state
 *  - 32 bytes for the byte-mask constant
 *
 * We need an additional 32 bytes for the message-length parameter (it's only 4
 * bytes, but all other data needs 32-byte alignment). That leaves 2648 bytes
 * for the message, or 41 64-byte message chunks.
 */
.balign 32
.globl msg
msg:
.zero 2648

.data

/**
 * Starting hash state.
 *
 * Represented in big-endian order to match FIPS 180-4, so the first word in
 * this sequence is H[7] and the last is H[0].
 *
 * Defaults to the initial SHA-256 hash state. To save and later resume a
 * partial hash computation, read the state and overwrite this buffer on the
 * next call with the saved state.
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
