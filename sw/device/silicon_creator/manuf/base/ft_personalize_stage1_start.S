// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

  .section .sram_start, "ax"
  .global sram_start
  .global _ottf_start
  .type sram_start, @function
sram_start:
_ottf_start:
  // Disable interrupts
  csrci mstatus, 8

  // Set up stack pointer to top of main SRAM (0x10020000)
  li sp, 0x10020000

  // Clear BSS segment
  la t0, _bss_start
  la t1, _bss_end
.L_clear_bss_loop:
  bge t0, t1, .L_clear_bss_done
  sw zero, 0(t0)
  addi t0, t0, 4
  j .L_clear_bss_loop
.L_clear_bss_done:

  // Jump to C main function
  tail main

  .size sram_start, .-sram_start
