/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

  /* Check that we trigger an error if a loop ends with another loop instruction */
  addi  x2, x0, 1

  loopi 1, 2
   addi  x3, x0, 1
   loopi 1, 1

  /* We shouldn't get here */
  nop
  addi  x4, x0, 1
  ecall
