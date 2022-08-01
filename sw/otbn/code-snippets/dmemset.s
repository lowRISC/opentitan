/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start
/* Test entry point, no arguments need to be passed in nor results returned. */
.globl main
main:
  jal x0, dmemset

.text
dmemset:
  la x2, set_value
  bn.lid x0, 0(x2)
  li x2, 0
  loopi 128, 1
    bn.sid x0, 0(x2++)
  ecall

.data
/* imput data to dmemset function. */
.globl set_value
.balign 32
set_value:
  .zero 32
