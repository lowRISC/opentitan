/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  Bad instruction address and branch at end of loop
*/
  loopi 1, 1
   beq x0, x0, .+2
