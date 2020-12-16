// Copyright lowRISC contributors.
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
 * Interrupt vectors in Ibex have 32 entries for 32 possible interrupts. The
 * vector must be 256-byte aligned, as Ibex's vectoring mechanism requires that.
 *
 * The ROM_EXT uses the address directly after the first possible interrupt
 * vector when starting execution after Mask ROM, which we choose to make look
 * like an extra entry. This is designed to match how Ibex chooses to implement
 * its initial execution address after boot.
 *
 * Thus this vector has exactly 33 4-byte entries.
 *
 * Only the following will be used by Ibex:
 * - Exception Handler (Entry 0)
 * - Machine Software Interrupt Handler (Entry 3)
 * - Machine Timer Interrupt Handler (Entry 7)
 * - Machine External Interrupt Handler (Entry 11)
 * - Vendor Interrupt Handlers (Entries 16-31)
 * - Reset Handler (Entry 32)
 *
 * More information about Ibex's interrupts can be found here:
 *   https://ibex-core.readthedocs.io/en/latest/03_reference/exception_interrupts.html
 */
  .balign 256
  .globl _rom_ext_interrupt_vector
  .type _rom_ext_interrupt_vector, @function
_rom_ext_interrupt_vector:

  // RISC-V Standard (Vectored) Interrupt Handlers:

  // Exception and User Software Interrupt Handler.
  unimp
  // Supervisor Software Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine Software Interrupt Handler.
  unimp

  // User Timer Interrupt Handler.
  unimp
  // Supervisor Timer Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine Timer Interrupt Handler.
  unimp

  // User External Interrupt Handler.
  unimp
  // Supervisor External Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine External Interrupt Handler.
  unimp

  // Reserved.
  unimp
  unimp
  unimp
  unimp

  // Vendor Interrupt Handlers:

  // On Ibex interrupt ids 30-16 are for "fast" interrupts.
  .rept 15
  unimp
  .endr

  // On Ibex interrupt id 31 is for non-maskable interrupts.
  unimp

  /**
   * ROM_EXT entry point.
   *
   * ROM_EXT is the second boot stage, which means that
   * this entry will be hit as a result of the jump from the Mask ROM, and
   * not the power-on. This indirection insures that Mask ROM has a well
   * defined address to jump to.
   */
  j _rom_ext_start_boot

  // Set size so this vector can be disassembled.
  .size _rom_ext_interrupt_vector, .-_rom_ext_interrupt_vector

  // Re-enable compressed instructions, linker relaxation.
  .option pop


/**
 * ROM_EXT runtime initialization code.
 */

  /**
   * NOTE: The "ax" flag below is necessary to ensure that this section
   * is allocated executable space in ROM by the linker.
   */
  .section .crt, "ax"

  /**
   * Linker Relaxation is disabled until `__global_pointer$` is setup, below,
   * because otherwise some sequences may be turned into gp-relative sequences,
   * which is incorrect when `gp` is not initialized.
   */
  .option push
  .option norelax

/**
 * Entry point.
 *
 * This symbol is jumped to from `_rom_ext_interrupt_vector + (32 * 4)`, and
 * is part of a two jump Mask ROM execution handover to ROM_EXT (`mask_rom_boot`
 * -> `_rom_ext_interrupt_vector + (32 * 4)` -> `_rom_ext_start_boot`).
 */
  .globl _rom_ext_start_boot
  .type _rom_ext_start_boot, @function
_rom_ext_start_boot:

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
   * Set well-defined interrupt/exception handlers
   *
   * The lowest two bits should be `0b01` to ensure we use vectored interrupts.
   */
  la   t0, _rom_ext_interrupt_vector
  andi t0, t0, -4
  ori  t0, t0, 0b01
  csrw mtvec, t0

  /**
   * Setup C Runtime
   */

  /**
   * Initialize the `.data` section in RAM from ROM.
   */
  la   a0, _data_start
  la   a1, _data_end
  la   a2, _data_init_start
  .extern crt_section_copy
  call crt_section_copy

  /**
   * Initialize the `.bss` section.
   *
   * We do this despite zeroing all of SRAM above, so that we still zero `.bss`
   * once we've enabled SRAM scrambling.
   */
  la   a0, _bss_start
  la   a1, _bss_end
  .extern crt_section_clear
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
   * Setup global pointer.
   *
   * This requires that we disable linker relaxations, or it will be relaxed to
   * `mv gp, gp`, so we disabled relaxations for all of `_mask_rom_start_boot`.
   */
  la gp, __global_pointer$

  // Re-enable linker relaxation.
  .option pop

  /**
   * Jump to C Code
   */
  .extern rom_ext_boot
  tail rom_ext_boot

  // Set size so this function can be disassembled.
  .size _rom_ext_start_boot, .-_rom_ext_start_boot
