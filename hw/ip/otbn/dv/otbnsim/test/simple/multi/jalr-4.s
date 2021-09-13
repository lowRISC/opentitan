/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  Overflow call stack and bad target and jump at end of loop
*/
  loopi 8, 1
    addi x1, x0, 0

  loopi 1, 1
    jalr x1, x0, 1
