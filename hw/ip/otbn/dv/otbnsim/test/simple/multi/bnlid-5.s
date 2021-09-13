/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  Bad WDR index and bad address
*/
  addi   x2, x0, 1
  addi   x3, x0, 100
  bn.lid x3, 0(x2)
