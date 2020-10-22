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
 *   https://ibex-core.readthedocs.io/en/latest/exception_interrupts.html
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
  mv x1,  zero
  // NOT x2 (sp) - We have already set it to the right value above.
  mv x3,  zero
  mv x4,  zero
  mv x5,  zero
  mv x6,  zero
  mv x7,  zero
  mv x8,  zero
  mv x9,  zero
  mv x10, zero
  mv x11, zero
  mv x12, zero
  mv x13, zero
  mv x14, zero
  mv x15, zero
  mv x16, zero
  mv x17, zero
  mv x18, zero
  mv x19, zero
  mv x20, zero
  mv x21, zero
  mv x22, zero
  mv x23, zero
  mv x24, zero
  mv x25, zero
  mv x26, zero
  mv x27, zero
  mv x28, zero
  mv x29, zero
  mv x30, zero
  mv x31, zero

  // TODO: Setup SRAM Scrambling
  // Temporarily: Zero out ram_main
  //
  // `t0` is the address to start zeroing at.
  // `t1` is the address to stop zeroing at.
  li   t0, TOP_EARLGREY_RAM_MAIN_BASE_ADDR
  li   t1, (TOP_EARLGREY_RAM_MAIN_BASE_ADDR + TOP_EARLGREY_RAM_MAIN_SIZE_BYTES)
  bgeu t0, t1, sram_zero_end
sram_zero_loop:
  // TODO: Unroll loop
  sw   zero, 0x0(t0)
  addi t0, t0, 0x4
  bltu t0, t1, sram_zero_loop
sram_zero_end:

  /**
   * Setup C Runtime
   */

  // Initialize the `.data` section.
  //
  // `t0` is the start address of `.data` (in RAM).
  // `t1` is the end address of `.data` (in RAM).
  // `t2` is the start address of `.data` (in ROM).
  // `t3` is a scratch register for the copy.
  la   t0, _data_start
  la   t1, _data_end
  la   t2, _data_init_start
  bgeu t0, t1, data_copy_loop_end
data_copy_loop:
  // TODO: Unroll this loop
  lw   t3, 0x0(t2)
  sw   t3, 0x0(t0)
  addi t0, t0, 0x4
  addi t2, t2, 0x4
  bltu t0, t1, data_copy_loop
data_copy_loop_end:

  // Initialize the `.bss` section.
  //
  // We do this despite zeroing all of SRAM above, so that we still zero `.bss`
  // once we've enabled SRAM scrambling.
  //
  // `t0` is the address to start zeroing at.
  // `t1` is the address to stop zeroing at.
  la   t0, _bss_start
  la   t1, _bss_end
  bgeu t0, t1, bss_zero_end
bss_zero_loop:
  // TODO: Unroll loop
  sw   zero, 0x0(t0)
  addi t0, t0, 0x4
  bltu t0, t1, bss_zero_loop
bss_zero_end:

  // Re-clobber all of the registers used to Setup the C Runtime.
  mv t0, zero
  mv t1, zero
  mv t2, zero
  mv t3, zero

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
