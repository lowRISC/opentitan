/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.equ START,               1
.equ COVFUNC_NESTED_HIT,  2
.equ COVFUNC_HIT,         4
.equ COVFUNC_NESTED_MISS, 8
.equ COVFUNC_MISS,        16
.equ COVFUNC_BSS_SKIP,    32


.section .text.start
start:
  addi  x5, x5, START
  jal   x1, covfunc_hit
  ecall

covfunc_nested_hit:
  addi  x5, x5, COVFUNC_NESTED_HIT
  ret

covfunc_hit:
  addi  x5, x5, COVFUNC_HIT
  jal   x1, covfunc_nested_hit
  ret

covfunc_nested_miss:
  addi  x5, x5, COVFUNC_NESTED_MISS
  ret

covfunc_miss:
  addi  x5, x5, COVFUNC_MISS
  jal   x1, covfunc_nested_miss
  ret

.bss

.globl covfunc_bss_skip
.balign 4
covfunc_bss_skip:
.zero COVFUNC_BSS_SKIP
