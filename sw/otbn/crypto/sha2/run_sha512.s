/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start
main:
  /* Load the number of 1024-bit message chunks.
       x30 <= dmem[n_chunks] */
  la     x2, n_chunks
  lw     x30, 0(x2)

  /* Run the masked sha512 process and update the state shares.
       dmem[state_s0, state_s1] = sha512_masked(dmem[state_s0, state_s1],
                                                dmem[msg_s0..msg_s0+x30*128],
                                                dmem[msg_s1..msg_s1+x30*128]) */
  la     x10, msg_s0
  la     x11, msg_s1
  jal    x1, sha512_masked

  ecall

.bss

/**
 * Hash state shares (512 bits = 64 bytes each).
 */
.balign 32
.globl state_s0
state_s0:
.zero 64

.balign 32
.globl state_s1
state_s1:
.zero 64

/**
 * Input message shares (must already be padded and boolean-shared).
 *
 * Out of 3072 bytes of bus-accessible DMEM:
 * - sha512_masked uses 736 bytes (.data constants)
 * - state_s0 + state_s1 uses 128 bytes
 * - msg_s0 + msg_s1 uses 2 * (8 * 128) = 2048 bytes (8 blocks per run)
 * - n_chunks uses 4 bytes
 * Total DMEM used: 2916 bytes.
 */
.balign 32
.globl msg_s0
msg_s0:
.zero 1024

.balign 32
.globl msg_s1
msg_s1:
.zero 1024

/**
 * Number of 1024-bit message chunks to process.
 */
.balign 4
.globl n_chunks
n_chunks:
.zero 4
