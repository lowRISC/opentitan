/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

  addi  x2, x0, 0x111
  addi  x3, x0, 0x222
  add   x4, x2, x3 /* for otbn_wfi_sec_wipe_vseq insn before wfi must be single cycle. */
  wfi

  /* Some instructions after the WFI so it is not the last instruction which could make it hard
   * to target the WFI instruction in the vseq.
   */
  addi  x2, x0, 0
  lw    x5, 0(x2)

  ecall
