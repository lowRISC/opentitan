// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_darjeeling/sw/autogen/top_darjeeling_memory.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/base/multibits_asm.h"
#include "otp_ctrl_regs.h"
#include "sram_ctrl_regs.h"

/**
 * Test ROM interrupt vectors.
 *
 * After reset all interrupts are disabled. Only exceptions (interrupt 0) and
 * non-maskable interrupts (interrupt 31) are possible. For simplicity however
 * we just set all interrupt handlers in the Test ROM to use the same handler,
 * which loops forever.
 *
 * Interrupt vectors in Ibex have 32 entries for 32 possible interrupts. The
 * vector must be 256-byte aligned, as Ibex's vectoring mechanism requires that.
 *
 * Note that the Ibex reset handler (entry point) immediately follows this
 * interrupt vector and can be thought of as an extra entry.
 *
 * More information about Ibex's interrupts can be found here:
 *   https://ibex-core.readthedocs.io/en/latest/03_reference/exception_interrupts.html
 */

  // Push Test second ROM interrupt vector options.
  .option push

  // Disable RISC-V instruction compression: we need all instructions to
  // be exactly word wide in the interrupt vector.
  .option norvc

  // Disable RISC-V linker relaxation, as it can compress instructions at
  // link-time, which we also really don't want.
  .option norelax

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated executable space in ROM by the linker.
  .section .vectors, "ax"
  .balign 256
  .global _test_rom_interrupt_vector
  .type _test_rom_interrupt_vector, @function
_test_rom_interrupt_vector:

  // Each jump instruction must be exactly 4 bytes in order to ensure that the
  // entries are properly located.
  .rept 32
  j _test_rom_irq_handler
  .endr

  // Ibex reset vector, the initial entry point after reset. (This falls at IRQ
  // handler 0x80.)
  j _second_rom_reset_start

  // Set size so this vector can be disassembled.
  .size _test_rom_interrupt_vector, .-_test_rom_interrupt_vector

  // Pop ROM interrupt vector options.
  //
  // Re-enable compressed instructions, linker relaxation.
  .option pop

// -----------------------------------------------------------------------------

/**
 * Test second ROM runtime initialization code.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated executable space in ROM by the linker.
  .section .crt, "ax"

  /**
   * Entry point after reset. This symbol is jumped to from the handler
   * for IRQ 0x80.
   */
  .balign 4
  .global _second_rom_reset_start
  .type _second_rom_reset_start, @function
_second_rom_reset_start:

  // Set up the global pointer. This requires that we disable linker relaxations
  // (or it will be relaxed to `mv gp, gp`).
  .option push
  .option norelax
  la  gp, __global_pointer$
  .option pop

  // Clobber all writeable registers.
  li  x1, 0x0
  li  x2, 0x0
  li  x4, 0x0
  li  x5, 0x0
  li  x6, 0x0
  li  x7, 0x0
  li  x8, 0x0
  li  x9, 0x0
  li  x10, 0x0
  li  x11, 0x0
  li  x12, 0x0
  li  x13, 0x0
  li  x14, 0x0
  li  x15, 0x0
  li  x16, 0x0
  li  x17, 0x0
  li  x18, 0x0
  li  x19, 0x0
  li  x20, 0x0
  li  x21, 0x0
  li  x22, 0x0
  li  x23, 0x0
  li  x24, 0x0
  li  x25, 0x0
  li  x26, 0x0
  li  x27, 0x0
  li  x28, 0x0
  li  x29, 0x0
  li  x30, 0x0
  li  x31, 0x0

  // Set up the stack.
  la  sp, _stack_end


  // Explicit fall-through to `_start`.
  .size _second_rom_reset_start, .-_second_rom_reset_start

// -----------------------------------------------------------------------------

  /**
   * Callable entry point for the boot rom.
   *
   * Currently, this zeroes the `.bss` section, copies initial data to
   * `.data`, and then jumps to the program entry point.
   */
  .balign 4
  .global _start
  .type _start, @function
_start:
  // Remove address space protections by configuring entry 15 as
  // read-write-execute for the entire address space and then clearing
  // all other entries.
  // NOTE: This should happen before attemting to access any address outside
  // the initial ePMP RX region at reset, e.g. `kDeviceType` which is in
  // .rodata.
  li   t0, (0x9f << 24) // Locked NAPOT read-write-execute.
  csrw pmpcfg3, t0
  li   t0, 0x7fffffff   // NAPOT encoded region covering entire 34-bit address space.
  csrw pmpaddr15, t0
  csrw pmpcfg0, zero
  csrw pmpcfg1, zero
  csrw pmpcfg2, zero

.L_sram_init_skip:
  // Zero out the `.bss` segment.
  la   a0, _bss_start
  la   a1, _bss_end
  call crt_section_clear

  // Initialize the `.data` segment from the `.idata` segment.
  la   a0, _data_start
  la   a1, _data_end
  la   a2, _data_init_start
  call crt_section_copy

  // Clobber all temporary registers.
  li t0, 0x0
  li t1, 0x0
  li t2, 0x0
  li t3, 0x0
  li t4, 0x0
  li t5, 0x0
  li t6, 0x0

  // Clobber all argument registers.
  li a0, 0x0
  li a1, 0x0
  li a2, 0x0
  li a3, 0x0
  li a4, 0x0
  li a5, 0x0
  li a6, 0x0
  li a7, 0x0

  // Jump into the C program entry point.
  call _boot_start

  // Enter a wait for interrupt loop, the device should reset shortly.
.L_wfi_loop:
  wfi
  j   .L_wfi_loop
  .size _start, .-_start

// -----------------------------------------------------------------------------

  /**
   * Test ROM IRQ/exception handler; loops forever.
   */
  .balign 4
  .section .text
  .global _test_rom_irq_handler
  .type _test_rom_irq_handler, @function
_test_rom_irq_handler:
  wfi
  j _test_rom_irq_handler
  .size _test_rom_irq_handler, .-_test_rom_irq_handler
