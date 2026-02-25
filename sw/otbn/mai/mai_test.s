/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
* Simple program to showcase how to use the MAI interface.
*/

.section .text.start
main:
  /* Load modulus */
  li      x2,  0
  la      x3,  mod32
  bn.lid  x2,  0(x3)
  bn.wsrw MOD, w0

  /* Configure MAI - select B2A */
  /* B2A requires the value 0x1 in the field operation. This field is in bits[2:1] */
  li    x2, 0x2
  csrrs x0, MAI_CTRL, x2
  csrrs x3, MAI_STATUS, x0 /* Optional, just to populate the trace */

  /* Write data into input WSRs */
  bn.wsrw MAI_IN0_S0, w1
  bn.wsrw MAI_IN0_S1, w2

  /* Start conversion by writing the start bit */
  li    x2, 0x1
  csrrs x3, MAI_STATUS, x0  /* Optional, just to populate the trace */
  csrrs x0, MAI_CTRL, x2
  /* Read the status register to populate the trace to see when the state changes. */
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  csrrs x3, MAI_STATUS, x0
  /* Poll busy bit - use this in production code */
_poll_busy:
  csrrs x2, MAI_STATUS, x0
  andi  x2, x2, 0x1
  bne   x2, x0, _poll_busy

  /* Read results from output WSRs */
  bn.wsrr w20, MAI_RES_S0
  bn.wsrr w21, MAI_RES_S1

  ecall

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
