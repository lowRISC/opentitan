/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  Underflow call stack for grs2 and bad address
*/
  addi   x2, x0, 1
  bn.sid x1, 0(x2)
