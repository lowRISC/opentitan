/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  Bad instruction address and branch at end of loop
*/
  addi x1, x0, 1
  loopi 1, 1
   bne x1, x0, .+2
