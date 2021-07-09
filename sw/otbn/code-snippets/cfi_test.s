/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text

.globl main
main:
  addi x10, x0, 7
  sw x10, 0(x0)
  ecall

.section .data

.globl rv
rv:
  .zero 4
