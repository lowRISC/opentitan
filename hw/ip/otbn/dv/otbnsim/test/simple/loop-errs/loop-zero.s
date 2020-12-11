/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

  /* Check that a zero count on a loop triggers an error. */
  addi  x2, x0, 1
  addi  x3, x0, 0

  loop x3, 1
   addi x2, x2, 1

  /* We shouldn't get here */
  addi x2, x2, 2
  ecall
