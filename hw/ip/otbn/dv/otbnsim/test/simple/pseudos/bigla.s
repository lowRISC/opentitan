/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    Checks for "la" pseudo-instruction support where the symbol is too big to
    fit in a signed immediate for addi.

    Rather awkwardly, this means we need to pick an address that's
    bigger than the DMEM region that's accessible over the bus. Use an
    IMEM location instead, and check it by branching through the
    pointer with JALR.

*/
.text
  la x2, foo
  jalr x3, x2, 0

.org 4088
foo:
  addi x4, x0, 1
  ecall
