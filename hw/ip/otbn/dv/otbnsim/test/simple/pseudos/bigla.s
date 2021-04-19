/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    Checks for "la" pseudo-instruction support where the symbol is too big to
    fit in a signed immediate for addi.
*/
.text
  la x2, foo
  lw x3, 0(x2)
  ecall

.data
.org 2048
foo:
  .word 0x1234
