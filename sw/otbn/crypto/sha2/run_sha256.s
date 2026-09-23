/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start
main:
  /* Load the number of message chunks.
       x30 <= dmem[num_msg_chunks] */
  la     x2, num_msg_chunks
  lw     x30, 0(x2)

  /* Run the masked sha256 process and update the state shares.
       dmem[state_s0, state_s1] = sha256_masked(dmem[state_s0, state_s1],
                                                dmem[msg_s0..msg_s0+x30*64],
                                                dmem[msg_s1..msg_s1+x30*64]) */
  la     x10, msg_s0
  la     x11, msg_s1
  jal    x1, sha256_masked

  ecall

.bss

/**
 * Hash state shares (256 bits each).
 */
.balign 32
.globl state_s0
state_s0:
.zero 32

.balign 32
.globl state_s1
state_s1:
.zero 32

/**
 * Input message shares (must already be padded and boolean-shared).
 *
 * Out of 3072 bytes of bus-accessible DMEM:
 * - sha256_masked uses 288 bytes (.data constants)
 * - state_s0 + state_s1 uses 64 bytes
 * - msg_s0 + msg_s1 uses 2 * (20 * 64) = 2560 bytes (up to 20 blocks per run)
 * - num_msg_chunks uses 4 bytes
 * Total DMEM used: 2916 bytes (zero alignment padding holes).
 */
.balign 32
.globl msg_s0
msg_s0:
.zero 1280

.balign 32
.globl msg_s1
msg_s1:
.zero 1280

/* Length of message (in 512-bit chunks). */
.balign 4
.globl num_msg_chunks
num_msg_chunks:
.zero 4
