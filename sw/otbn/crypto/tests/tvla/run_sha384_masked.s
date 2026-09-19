/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start
main:
  /* Set the number of message chunks (1 block of 1024 bits) */
  li      x30, 1

  /* Load pointers to Share 0 and Share 1 of the padded message */
  la      x10, msg_s0
  la      x11, msg_s1

  /* Run the SHA-384 masked process */
  jal     x1, sha384_masked

  ecall

.data

.balign 32
.globl msg_s0
msg_s0:
.zero 128

.balign 32
.globl msg_s1
msg_s1:
.zero 128

.balign 32
.globl state_s0
state_s0:
.zero 64

.balign 32
.globl state_s1
state_s1:
.zero 64
