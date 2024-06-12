// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"

/**
 * ROM_EXT Interrupt Vector
 */
  .section .vectors, "ax"
  .option push

  // Disable RISC-V instruction compression: we need all instructions to
  // be exactly word wide in the interrupt vector.
  .option norvc

  // Disable RISC-V linker relaxation, as it can compress instructions at
  // link-time, which we also really don't want.
  .option norelax

  /**
   * `_rom_ext_interrupt_vector` is an ibex-compatible interrupt vector.
   *
   * Interrupt vectors in Ibex have 32 4-byte entries for 32 possible interrupts.
   * The vector must be 256-byte aligned, as Ibex's vectoring mechanism
   * requires that. This section will be padded with `unimp` (`0xc0001073`) if
   * needed depending on the alignment of the next section.
   *
   * Only the following will be used by Ibex:
   * - Exception Handler (Entry 0)
   * - Machine Software Interrupt Handler (Entry 3)
   * - Machine Timer Interrupt Handler (Entry 7)
   * - Machine External Interrupt Handler (Entry 11)
   * - Vendor Interrupt Handlers (Entries 16-31)
   *
   * More information about Ibex's interrupts can be found here:
   *   https://ibex-core.readthedocs.io/en/latest/03_reference/exception_interrupts.html
   */
  .balignl 256, 0xc0001073
  .global _rom_ext_interrupt_vector
  .type _rom_ext_interrupt_vector, @function
_rom_ext_interrupt_vector:
  // Entry 0: exception handler.
  j rom_ext_exception_handler

  // Entries 1-30: interrupt handlers.
  .rept 30
  j rom_ext_interrupt_handler
  .endr

  // Entry 31: non-maskable interrupt handler.
  j rom_ext_nmi_handler
  .size _rom_ext_interrupt_vector, .-_rom_ext_interrupt_vector

  // Re-enable compressed instructions, linker relaxation.
  .option pop

// -----------------------------------------------------------------------------

/**
 * ROM_EXT runtime initialization code.
 */

  /**
   * NOTE: The "ax" flag below is necessary to ensure that this section
   * is allocated executable space in ROM by the linker.
   */
  .section .crt, "ax"

  /**
   * Entry point.
   *
   * This symbol is jumped to from `rom_boot` using the `entry_point` field
   * of the manifest.
   */
  .balign 4
  .global _rom_ext_start_boot
  .type _rom_ext_start_boot, @function
_rom_ext_start_boot:
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
   * word in the stack into sp.
   *
   * If an exception fires, the handler is conventionaly only allowed to clobber
   * memory at addresses below `sp`.
   */
  la   sp, _stack_end

  /**
   * Setup C Runtime
   */

  /**
   * Initialize the `.data` section in RAM from ROM.
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
   * Set well-defined interrupt/exception handlers
   *
   * The lowest two bits should be `0b01` to ensure we use vectored interrupts.
   * We set the handlers only after making sure that we can execute some code,
   * i.e. `crt_section_copy` and `crt_section_clear`, to avoid a double-fault
   * condition. Any exceptions and interrupts occuring before this line will be
   * handled by the ROM.
   */
  la   t0, (_rom_ext_interrupt_vector + 1)
  csrw mtvec, t0

  /**
   * Jump to C Code
   */
  tail rom_ext_main
  .size _rom_ext_start_boot, .-_rom_ext_start_boot
