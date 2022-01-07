// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"
#include "sram_ctrl_regs.h"
#include "entropy_src_regs.h"
#include "csrng_regs.h"
#include "edn_regs.h"

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

  // Push Test ROM interrupt vector options.
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
  .globl _test_rom_interrupt_vector
  .type _test_rom_interrupt_vector, @function
_test_rom_interrupt_vector:

  // Each jump instruction must be exactly 4 bytes in order to ensure that the
  // entries are properly located.
  .rept 32
  j _test_rom_irq_handler
  .endr

  // Ibex reset vector, the initial entry point after reset. (This falls at IRQ
  // handler 0x80.)
  j _reset_start

  // Set size so this vector can be disassembled.
  .size _test_rom_interrupt_vector, .-_test_rom_interrupt_vector

  // Pop Mask ROM interrupt vector options.
  //
  // Re-enable compressed instructions, linker relaxation.
  .option pop

/**
 * Test ROM runtime initialization code.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated executable space in ROM by the linker.
  .section .crt, "ax"

  .extern crt_section_clear
  .extern crt_section_copy

/**
 * Entry point after reset. This symbol is jumped to from the handler
 * for IRQ 0x80.
 */
_reset_start:
  .globl _reset_start
  // Clobber all writeable registers.
  li  x1, 0x0
  li  x2, 0x0
  li  x3, 0x0
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

  // Set up the global pointer. This requires that we disable linker relaxations
  // (or it will be relaxed to `mv gp, gp`).
  .option push
  .option norelax
  la  gp, __global_pointer$
  .option pop

  // Explicit fall-through to `_start`.

/**
 * Callable entry point for the boot rom.
 *
 * Currently, this zeroes the `.bss` section, copies initial data to
 * `.data`, and then jumps to the program entry point.
 */
_start:
  .globl _start

  // Enable entropy complex - this is not the full enable
  li   a0, TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR
  li   t0, 0x55505a
  sw   t0, ENTROPY_SRC_CONF_REG_OFFSET(a0)

  li   a0, TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR
  li   t0, 0xa
  sw   t0, ENTROPY_SRC_MODULE_ENABLE_REG_OFFSET(a0)

  li   a0, TOP_EARLGREY_CSRNG_BASE_ADDR
  li   t0, 0xaaa
  sw   t0, CSRNG_CTRL_REG_OFFSET(a0)

  li   a0, TOP_EARLGREY_EDN0_BASE_ADDR
  li   t0, 0x55aa
  sw   t0, EDN_CTRL_REG_OFFSET(a0)

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

/**
 * Test ROM IRQ/exception handler; loops forever.
 */

  // Put this handler in the code section.
 .section .text

_test_rom_irq_handler:
  wfi
  j _test_rom_irq_handler
