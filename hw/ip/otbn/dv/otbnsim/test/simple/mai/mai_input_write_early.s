/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
  Write an input WSR as the 8th instruction after the START write of a secAdd.

  In the RTL, INPUT_READY still reads 0 in that cycle, so the write raises
  MAI_SOFTWARE_ERROR.
*/

  bn.xor    w0, w0, w0
  bn.wsrw   MAI_IN0_S0, w0
  bn.wsrw   MAI_IN0_S1, w0
  bn.wsrw   MAI_IN1_S0, w0
  bn.wsrw   MAI_IN1_S1, w0

  li        x10, 0x2f
  csrrw     x0, MAI_CTRL, x10
  .rept 7
  addi      x0, x0, 0
  .endr
  bn.wsrw   MAI_IN0_S0, w0

  ecall
