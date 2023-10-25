// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"

/**
 * Runtime initialization code.
 */

  /**
   * NOTE: The "ax" flag below is necessary to ensure that this section
   * is allocated executable space by the linker.
   */
  .section .crt, "ax"

  /**
   * Entry point.
   */
  .balign 4
  .global _start_boot
  .type _start_boot, @function
_start_boot:
  /**
   * Set up the global pointer `gp`.
   *
   * Linker relaxations are disabled until the global pointer is setup below,
   * because otherwise some sequences may be turned into `gp`-relative
   * sequences, which is incorrect when `gp` is not initialized.
   */
  .option push
  .option norelax
  la gp, __global_pointer$
  .option pop

  /**
   * Disable Interrupts.
   *
   * We cannot disable exceptions, or Ibex's non-maskable interrupts (interrupt
   * 31), so we still need to be careful.
   */

  // Clear `MIE` field of `mstatus` (disable interrupts globally).
  csrci mstatus, 0x8

  /**
   * Clear all the machine-defined interrupts, `MEIE`, `MTIE`, and `MSIE` fields
   * of `mie`.
   */
  li   t0, 0xFFFF0888
  csrc mie, t0

  /**
   * Set up the stack pointer.
   *
   * In RISC-V, the stack grows downwards, so we load the address of the highest
   * word in the stack into sp. We don't load in `_stack_end`, as that points
   * beyond the end of RAM, and we always want it to be valid to dereference
   * `sp`, and we need this to be 128-bit (16-byte) aligned to meet the psABI.
   *
   * If an exception fires, the handler is conventionaly only allowed to clobber
   * memory at addresses below `sp`.
   */
  la   sp, (_stack_end - 16)

  /**
   * Do NOT set interrupt/exception handlers.  We want to leave the ROM_EXT
   * handlers in place so we can verify them.
   *
   * la   t0, (_interrupt_vector + 1)
   * csrw mtvec, t0
   */

  /**
   * Setup C Runtime
   */

  /**
   * Initialize the `.data` section in RAM from RO memory.
   */
  la   a0, _data_start
  la   a1, _data_end
  la   a2, _data_init_start
  call crt_section_copy

  /**
   * Initialize the `.bss` section.
   *
   * We do this despite zeroing all of SRAM above, so that we still zero `.bss`
   * once we've enabled SRAM scrambling.
   */
  la   a0, _bss_start
  la   a1, _bss_end
  call crt_section_clear

  // Re-clobber all of the temporary registers.
  li t0, 0x0
  li t1, 0x0
  li t2, 0x0
  li t3, 0x0
  li t4, 0x0
  li t5, 0x0
  li t6, 0x0

  // Re-clobber all of the argument registers.
  li a0, 0x0
  li a1, 0x0
  li a2, 0x0
  li a3, 0x0
  li a4, 0x0
  li a5, 0x0
  li a6, 0x0
  li a7, 0x0

  /**
   * Jump to C Code
   */
  tail fault_test_main
  .size _start_boot, .-_start_boot
