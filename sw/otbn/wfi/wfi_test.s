/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
 * OTBN application to test the WFI instruction.
 *
 * Flow:
 * - Host stores a random value to `input` before start.
 * - OTBN copies `input` to `output`, then pauses on the 1st WFI.
 * - Host reads `output` and writes a 2nd random word into `input`.
 * - Host issues RESUME. OTBN copies `input` to `output`, then pauses on the 2nd WFI.
 * - Host issues RESUME again. OTBN finishes.
 *
 * This lets the host confirm that:
 * - the code before the 1st WFI ran,
 * - it can access DMEM while OTBN is paused,
 * - execution resumed after the 1st WFI and can see the host's write,
 * - OTBN can pause more than once.
 *
 * WFI is only legal while CTRL.wfi_enabled is set, so the host must enable it before starting this
 * program.
 */

.section .text.start

  la    x2, input
  la    x3, output

  /* Copy the 1st random value */
  lw    x4, 0(x2)
  sw    x4, 0(x3)
  wfi

  /* Copy the 2nd random value */
  lw    x4, 0(x2)
  sw    x4, 0(x3)
  wfi

  ecall

.section .data

.balign 32
.globl input
input:
  .word 0x00000000

.balign 32
.globl output
output:
  .word 0x00000000
