/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  Underflow call stack and branch at end of loop
*/
  loopi 1, 1
   bne x1, x1, foo

  ecall
foo:
  nop
  ecall
