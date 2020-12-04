/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test to trigger a BadDataAddr error */

.section .text

/* Test entry point, no arguments need to be passed in nor results returned */
.globl err_test
err_test:
  /* Trigger a BadDataAddr by reading from an unaligned address */
  li x2, 0x3
  lw x3, 0(x2)

  ecall
