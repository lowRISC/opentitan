/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * A simple program showcasing how to use the MAI and testing it by
 * performing a B2A conversion followed by an A2B conversion.
 */
.global main

.text

main:
  /* Load modulus */
  li x2, 30
  la x3, mod32
  bn.lid x2, 0(x3)
  bn.wsrw MOD, w30

  /* Optional: Dump the initial state to the trace */
  csrrs x4, MAI_CTRL, x0
  csrrs x3, MAI_STATUS, x0

  /* Configure MAI - select B2A */
  /* B2A requires the value 0x1 in the field operation. This field is in bits[2:1] */
  li x2, 0x2
  csrrs x0, MAI_CTRL, x2

  /* Add boolean mask to the secret in w0 */
  bn.wsrr w2, URND
  bn.xor w1, w0, w2

  /* Write shares to input WSRs */
  bn.wsrw MAI_IN0_S0, w1
  bn.wsrw MAI_IN0_S1, w2

  /* Optional: Check if MAI is ready - Bit 1 must be set */
  csrrs x3, MAI_STATUS, x0
  andi x3, x3, 0x2
  beq x3, x0, _mai_error

  /* Start conversion by writing the start bit */
  li x10, 0x1
  csrrs x3, MAI_STATUS, x0  /* Optional: Just to populate the trace */
  csrrs x4, MAI_CTRL, x0    /* Optional: Just to populate the trace */
  csrrs x0, MAI_CTRL, x10
  csrrs x4, MAI_CTRL, x0  /* Optional: Just to populate the trace */

  /* Poll busy bit */
  jal x1, _poll_busy

  /* Read arithmetically masked results from output WSRs */
  bn.wsrr w20, MAI_RES_S0
  bn.wsrr w21, MAI_RES_S1

  /* Convert them back to boolean masked domain */
  bn.wsrw MAI_IN0_s1, w20
  bn.wsrw MAI_IN0_s0, w21

  /* Configure MAI - select A2B */
  /* A2B requires the value 0x0 in the field operation. This field is in bits[2:1] */
  li x2, 0x0
  csrrw x0, MAI_CTRL, x2
  csrrs x4, MAI_CTRL, x0  /* Optional: Just to populate the trace */

  /* Start conversion by writing the start bit */
  li x10, 0x1
  csrrs x0, MAI_CTRL, x10

  jal x1, _poll_busy

  /* Read results from output WSRs */
  bn.wsrr w22, MAI_RES_S0
  bn.wsrr w23, MAI_RES_S1

  /* Unmask the secret */
  bn.xor w24, w22, w23

  ecall

_poll_busy:
  csrrs x2, MAI_STATUS, x0
  andi x2, x2, 0x1
  bne x2, x0, _poll_busy
  ret

_mai_error:
  unimp

.section .data

/*
  mod32 = 8380417
*/
mod32:
  .word 0x007fe001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
