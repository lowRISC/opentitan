// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"

/**
 * Mask ROM Interrupt Vector
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
 * `_mask_rom_interrupt_vector` is the boot-defined interrupt vector for Ibex,
 * for the Mask ROM.
 *
 * The Mask ROM does not use interrupts, so there are only entries for Ibex's
 * non-maskable interrupts, and for the hardware exception handler.
 *
 * Interrupt vectors in Ibex have 32 entries for 32 possible interrupts. The
 * vector must be 256-byte aligned, as Ibex's vectoring mechanism requires that.
 * Ibex uses the instruction directly after the boot interrupt vector when
 * starting execution from reset, which we choose to make look like an extra
 * entry.
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
  .globl _mask_rom_interrupt_vector
  .type _mask_rom_interrupt_vector, @function
_mask_rom_interrupt_vector:

  // RISC-V Standard (Vectored) Interrupt Handlers:

  // Exception and User Software Interrupt Handler.
  .extern mask_rom_exception_handler
  j mask_rom_exception_handler
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
  .extern mask_rom_nmi_handler
  j mask_rom_nmi_handler

  // Ibex Reset Handler:
  j _mask_rom_start_boot

  // Set size so this vector can be disassembled.
  .size _mask_rom_interrupt_vector, .-_mask_rom_interrupt_vector

  // Re-enable compressed instructions, linker relaxation.
  .option pop


/**
 * Mask ROM runtime initialization code.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated executable space in ROM by the linker.
  .section .crt, "ax"

  // Linker Relaxation is disabled until `__global_pointer$` is setup, below,
  // because otherwise some sequences may be turned into gp-relative sequences,
  // which is incorrect when `gp` is not initialized.
  .option push
  .option norelax

/**
 * Entry point after reset. This symbol is jumped to from the handler
 * for IRQ 32.
 *
 * then jumps to `mask_rom_boot
 */
  .globl _mask_rom_start_boot
  .type _mask_rom_start_boot, @function
_mask_rom_start_boot:

  /**
   * The interrupts are disabled globally on reset. However, We cannot disable
   * exceptions, or Ibex's non-maskable interrupts (interrupt 31), so we still
   * need to be careful.
   */

  // Clear all the machine-defined interrupts, `MEIE`, `MTIE`, and `MSIE` fields
  // of `mie`.
  li   t0, 0xFFFF0888
  csrc mie, t0

  // Set up the stack pointer.
  //
  // In RISC-V, the stack grows downwards, so we load the address of the highest
  // word in the stack into sp. We don't load in `_stack_end`, as that points
  // beyond the end of RAM, and we always want it to be valid to dereference
  // `sp`, and we need this to be 128-bit (16-byte) aligned to meet the psABI.
  //
  // If an exception fires, the handler is conventionaly only allowed to clobber
  // memory at addresses below `sp`.
  la   sp, (_stack_end - 16)

  /**
   * Set well-defined interrupt/exception handlers
   *
   * We actually booted with this value of `mtvec`, so we shouldn't need to do
   * this.
   *
   * The lowest two bits should be `0b01` to ensure we use vectored interrupts.
   */
  la   t0, _mask_rom_interrupt_vector
  andi t0, t0, -4
  ori  t0, t0, 0b01
  csrw mtvec, t0

  /**
   * Clean Device State Part 1 (Please refer to `boot.md` section "Cleaning Device
   * State").
   */

  // Zero all writable registers except x2 (sp).
  li x1,  0x0
  // NOT x2 (sp) - We have already set it to the right value above.
  li x3,  0x0
  li x4,  0x0
  li x5,  0x0
  li x6,  0x0
  li x7,  0x0
  li x8,  0x0
  li x9,  0x0
  li x10, 0x0
  li x11, 0x0
  li x12, 0x0
  li x13, 0x0
  li x14, 0x0
  li x15, 0x0
  li x16, 0x0
  li x17, 0x0
  li x18, 0x0
  li x19, 0x0
  li x20, 0x0
  li x21, 0x0
  li x22, 0x0
  li x23, 0x0
  li x24, 0x0
  li x25, 0x0
  li x26, 0x0
  li x27, 0x0
  li x28, 0x0
  li x29, 0x0
  li x30, 0x0
  li x31, 0x0

  .extern crt_section_clear
  .extern crt_section_copy

  // TODO: Setup SRAM Scrambling
  // Temporarily: Zero out ram_main
  li   a0, TOP_EARLGREY_RAM_MAIN_BASE_ADDR
  li   a1, (TOP_EARLGREY_RAM_MAIN_BASE_ADDR + TOP_EARLGREY_RAM_MAIN_SIZE_BYTES)
  call crt_section_clear

  /**
   * Setup C Runtime
   */

  // Initialize the `.data` section.
  la   a0, _data_start
  la   a1, _data_end
  la   a2, _data_init_start
  call crt_section_copy

  // Initialize the `.bss` section.
  //
  // We do this despite zeroing all of SRAM above, so that we still zero `.bss`
  // once we've enabled SRAM scrambling.
  la   a0, _bss_start
  la   a1, _bss_end
  call crt_section_clear

  // Re-clobber all of the temporary registers (may have been used in calls).
  li t0, 0x0
  li t1, 0x0
  li t2, 0x0
  li t3, 0x0
  li t4, 0x0
  li t5, 0x0
  li t6, 0x0

  // Re-clobber all of the argument registers (may have been used in calls).
  li a0, 0x0
  li a1, 0x0
  li a2, 0x0
  li a3, 0x0
  li a4, 0x0
  li a5, 0x0
  li a6, 0x0
  li a7, 0x0

  // Setup global pointer.
  //
  // This requires that we disable linker relaxations, or it will be relaxed to
  // `mv gp, gp`, so we disabled relaxations for all of `_mask_rom_start_boot`.
  la gp, __global_pointer$

  /**
   * Jump to C Code
   */
  .extern mask_rom_boot
  tail mask_rom_boot

  // Set size so this function can be disassembled.
  .size _mask_rom_start_boot, .-_mask_rom_start_boot

  // Re-enable linker relaxation.
  .option pop
