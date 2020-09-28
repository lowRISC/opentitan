/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

  addi    x10, x0, 1
  addi    x11, x0, -1

  /* 1 + 1 = 2 (x2 = 2) */
  add     x2, x10, x10

  /* 2 + 1 = 3 (x3 = 3) */
  add     x3, x2, x10

  /* 3 + (-1) = 2 (x4 = 2) */
  add     x4, x3, x11

  /* (-1) + (-1) = -2 (x5 = -2) */
  add     x5, x11, x11

  ecall
