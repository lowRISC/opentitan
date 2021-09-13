/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  Underflow call stack for grd and double increment and bad WDR index for grs
*/
  addi    x2, x0, 100
  bn.movr x1++, x2++
