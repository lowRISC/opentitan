// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/multibits_asm.h"
#include "ast_regs.h"
#include "csrng_regs.h"
#include "edn_regs.h"
#include "entropy_src_regs.h"
#include "otp_ctrl_regs.h"
#include "sensor_ctrl_regs.h"
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
  j _reset_start

  // Set size so this vector can be disassembled.
  .size _test_rom_interrupt_vector, .-_test_rom_interrupt_vector

  // Pop ROM interrupt vector options.
  //
  // Re-enable compressed instructions, linker relaxation.
  .option pop

// -----------------------------------------------------------------------------

/**
 * Test ROM runtime initialization code.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated executable space in ROM by the linker.
  .section .crt, "ax"

  /**
   * Entry point after reset. This symbol is jumped to from the handler
   * for IRQ 0x80.
   */
  .balign 4
  .global _reset_start
  .type _reset_start, @function
_reset_start:

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
  .size _reset_start, .-_reset_start

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
#if !OT_IS_ENGLISH_BREAKFAST
  // Check if AST initialization should be skipped.
  li   a0, (TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR + \
            OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET)
  lw   t0, OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_INIT_EN_OFFSET(a0)
  li   t1, MULTIBIT_ASM_BOOL4_TRUE
  bne  t0, t1, .L_ast_init_skip

  // Copy the AST configuration from OTP.
  li   a0, (TOP_EARLGREY_AST_BASE_ADDR)
  li   a1, (TOP_EARLGREY_AST_BASE_ADDR + AST_REGAL_REG_OFFSET + 4)
  li   a2, (TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR + \
            OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET + \
            OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_CFG_OFFSET)
  call crt_section_copy

  // Wait for AST initialization to complete.
  li   a0, TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR
.L_ast_done_loop:
  lw   t0, SENSOR_CTRL_STATUS_REG_OFFSET(a0)
  srli t0, t0, SENSOR_CTRL_STATUS_AST_INIT_DONE_BIT // no-op as bit index is currently 0
  andi t0, t0, 0x1
  beqz t0, .L_ast_done_loop

.L_ast_init_skip:
  // The following sequence enables the minimum level of entropy required to
  // initialize memory scrambling, as well as the entropy distribution network.
  li a0, TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR
  // Note for BOOT_ROM initialization the FIPS_ENABLE bit is set to kMultiBitBool4False
  // to prevent the release of FIPS entropy until all the thresholds are set
  li t0, (MULTIBIT_ASM_BOOL4_FALSE << ENTROPY_SRC_CONF_FIPS_ENABLE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_FALSE << ENTROPY_SRC_CONF_ENTROPY_DATA_REG_ENABLE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_FALSE << ENTROPY_SRC_CONF_THRESHOLD_SCOPE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_FALSE << ENTROPY_SRC_CONF_RNG_BIT_ENABLE_OFFSET)
  sw t0, ENTROPY_SRC_CONF_REG_OFFSET(a0)

  li t0, (MULTIBIT_ASM_BOOL4_TRUE << ENTROPY_SRC_MODULE_ENABLE_MODULE_ENABLE_OFFSET)
  sw t0, ENTROPY_SRC_MODULE_ENABLE_REG_OFFSET(a0)

  li a0, TOP_EARLGREY_CSRNG_BASE_ADDR
  li t0, (MULTIBIT_ASM_BOOL4_TRUE << CSRNG_CTRL_ENABLE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_TRUE << CSRNG_CTRL_SW_APP_ENABLE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_TRUE << CSRNG_CTRL_READ_INT_STATE_OFFSET)
  sw t0, CSRNG_CTRL_REG_OFFSET(a0)

  li a0, TOP_EARLGREY_EDN0_BASE_ADDR
  li t0, (MULTIBIT_ASM_BOOL4_TRUE << EDN_CTRL_EDN_ENABLE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_TRUE << EDN_CTRL_BOOT_REQ_MODE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_FALSE << EDN_CTRL_AUTO_REQ_MODE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_FALSE << EDN_CTRL_CMD_FIFO_RST_OFFSET)
  sw t0, EDN_CTRL_REG_OFFSET(a0)

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
#endif
  // Scramble and initialize main memory (main SRAM).
  // Memory accesses will stall until initialization is complete.
  // Skip SRAM initialization for DV sim device type, as the testbench handles
  // this to optimize test run times.
  lw    t0, kDeviceType
  beqz  t0, .L_sram_init_skip
  li    a0, TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR
  li    t0, (1 << SRAM_CTRL_CTRL_INIT_BIT)
  sw    t0, SRAM_CTRL_CTRL_REG_OFFSET(a0)

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
