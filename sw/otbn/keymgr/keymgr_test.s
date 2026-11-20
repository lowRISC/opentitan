/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Simple keymgr interface test.
 *
 * Receives a message over the keymgr interface, discards it and then sends
 * back a fixed response defined by the host.
 */
.global main

.section .text.start

main:
  bn.xor w31, w31, w31

  jal x1, keymgr_init

  /* Receive the message but discard it. */
_receive_msg:
  jal x1, keymgr_rcv
  beq x20, x0, _receive_msg

  /* Load the fixed response.
   * w0, w1 contain share 0. w2, w3 contain share 1. */
  la x3, response_s0
  li x2, 0
  bn.lid x2, 0(x3++)
  li x2, 1
  bn.lid x2, 0(x3++)

  la x3, response_s1
  li x2, 2
  bn.lid x2, 0(x3++)
  li x2, 3
  bn.lid x2, 0(x3++)

  jal x1, keymgr_rsp

  ecall

.section .data

/* Fixed response */
.balign 32
.globl response_s0
response_s0:
  .zero 64

.globl response_s1
response_s1:
  .zero 64
