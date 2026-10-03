/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  BN.ADDV with the unsupported ELEN encoding 2'b01 (bn.addv.8s w3, w1, w2
  with bit 25 set). The assembler cannot encode it, so give the word directly.
*/
  .word 0x022081db
