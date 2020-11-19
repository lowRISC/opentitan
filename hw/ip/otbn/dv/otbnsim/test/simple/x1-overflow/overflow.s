/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
  An example of overflowing the x1 stack. Make sure that we stop execution and
  properly raise an alert. To avoid lots of copy-paste code, we just loop 100
  times, incrementing a variable as we go. This variable will contain the call
  stack depth when we stop.
*/
  addi x10, x0, 10
  addi  x2, x0, 0

  loopi 100, 2
  addi  x1, x0, 0
  addi  x2, x2, 1

  /* We shouldn't get here */
  addi x10, x0, 0
  ecall
