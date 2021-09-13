/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  Overflow call stack and bad target address
*/
  loopi 8, 1
    addi x1, x0, 0
  jal x1, .+2
