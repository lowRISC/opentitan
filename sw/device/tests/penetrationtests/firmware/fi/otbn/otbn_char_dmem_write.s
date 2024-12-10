/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR.DMEM_WRITE FI Penetration Test
*/
.section .text.start
  /* Just return back to Ibex as the target is the DMEM write. */

  ecall

.data
  .balign 32
  .globl mem
  mem:
    .zero 128
