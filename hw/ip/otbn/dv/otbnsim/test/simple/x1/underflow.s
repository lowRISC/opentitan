/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
  An example of underflowing the x1 stack. Make sure that we stop execution and
  properly raise an alert.
*/
  addi  x10, x0, 10

  /* Push once onto the stack */
  addi  x1, x0, 123
  /* Pop once from the stack: this should be fine */
  addi  x2, x1, 0

  /* Push once onto the stack */
  addi  x1, x0, 123
  /* Pop once from the stack (but with both input operands) */
  add   x3, x1, x1

  /* Pop again from the stack. ERROR! */
  addi  x0, x1, 0

  /* We shouldn't get here */
  addi x10, x0, 0
  ecall
