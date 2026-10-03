/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  BN.TRN1 with the reserved ELEN encoding 2'b11 (bn.trn1.8s w3, w1, w2
  with bits 26:25 set). The assembler cannot encode it, so give the word directly.
*/
  .word 0x0620d1db
