/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start
main:
  /* Set the state pointer. */
  la      x2, state
  la      x3, dptr_state
  sw      x2, 0(x3)

  /* Set the message pointer. */
  la      x2, msg
  la      x3, dptr_msg
  sw      x2, 0(x3)

  /* Run the sha512 process and update the state.
       dmem[state] = sha256(dmem[state], dmem[msg..msg+x30*64] */
  jal    x1, sha512

  ecall

.bss

/**
 * Number of 1024-bit message chunks to process.
 */
.balign 4
.globl n_chunks
n_chunks:
.zero 4

/**
 * Input message (must already be padded).
 *
 * The message size is limited by available DMEM space. Out of a bus-accessible
 * 3000 bytes, SHA-512 uses:
 * - 8*80 = 640 bytes for round constants
 * - 8*32 = 256 bytes for the hash state
 * - 32 bytes for small buffers (message length and pointers)
 *
 * The small buffers are less than 32 bytes total, but all other data needs
 * 32-byte alignment, so we can consider 32 bytes used.
 *
 * In total, that leaves 2072 bytes for the message, or up to 16 128-byte
 * message chunks.
 */
.balign 32
.globl msg
msg:
.zero 2072

.data

/**
 * Starting hash state.
 *
 * Represented in pre-processed form so that the 64 bits of each hash state
 * variable are in the least-significant position of a 256-bit word.
 *
 * Defaults to the initial SHA-512 hash state. To save and later resume a
 * partial hash computation, read the state and overwrite this buffer on the
 * next call with the saved state.
 */
.balign 32
.globl state
state:
.dword 0x6a09e667f3bcc908
  .balign 32
.dword 0xbb67ae8584caa73b
  .balign 32
.dword 0x3c6ef372fe94f82b
  .balign 32
.dword 0xa54ff53a5f1d36f1
  .balign 32
.dword 0x510e527fade682d1
  .balign 32
.dword 0x9b05688c2b3e6c1f
  .balign 32
.dword 0x1f83d9abfb41bd6b
  .balign 32
.dword 0x5be0cd19137e2179
