// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_darjeeling/sw/autogen/top_darjeeling_memory.h"
#include "sw/lib/sw/device/base/hardened_asm.h"
#include "sw/lib/sw/device/base/multibits_asm.h"
#include "sw/lib/sw/device/silicon_creator/base/chip.h"
#include "aon_timer_regs.h"
#include "ast_regs.h"
#include "clkmgr_regs.h"
#include "csrng_regs.h"
#include "edn_regs.h"
#include "gpio_regs.h"
#include "lc_ctrl_regs.h"
#include "otp_ctrl_regs.h"
#include "pinmux_regs.h"
#include "pwrmgr_regs.h"
#include "rv_core_ibex_regs.h"
#include "sensor_ctrl_regs.h"
#include "sram_ctrl_regs.h"

// This macro defines convenience labels for tests that use a debugger.
#define LABEL_FOR_TEST(kName_) .local kName_ ; kName_: ;

.equ UNIMP, 0xc0001073
.extern _epmp_second_text_tor_lo
.extern _epmp_second_text_tor_hi
/**
 * ROM interrupt vectors.
 */

  // Push ROM interrupt vector options.
  .option push

  // Disable RISC-V instruction compression: we need all instructions to
  // be exactly word wide in the interrupt vector.
  .option norvc

  // Disable RISC-V linker relaxation, as it can compress instructions at
  // link-time, which we also really don't want.
  .option norelax

  /**
   * Initial RISC-V vectored exception/interrupt handlers.
   *
   * After reset, all interrupts are disabled. Only exceptions (interrupt 0) and
   * non-maskable interrupts (interrupt 31) are possible. For simplicity,
   * however, we just set all interrupt handlers to the same exception handler.
   *
   * Since the C runtime is not initialized immediately after reset, the initial
   * interrupt vector must only call functions written in assembly. Once the C
   * runtime is intialized, the interrupt vector should be replaced.
   *
   * If the hardware is operating correctly, the assembly interrupt handlers
   * should never be called.
   *
   * Note that the Ibex reset handler (entry point) immediately follows this
   * interrupt vector and can be thought of as an extra entry.
   *
   * More information about Ibex's interrupts can be found here:
   *   https://ibex-core.readthedocs.io/en/latest/03_reference/exception_interrupts.html
   */
  .section .vectors, "ax"
  .balignl 256, UNIMP
  .global _rom_interrupt_vector_asm
  .type _rom_interrupt_vector_asm, @function
_rom_interrupt_vector_asm:
  // Each jump instruction must be exactly 4 bytes in order to ensure that the
  // entries are properly located.
  .rept 32
  j _asm_exception_handler
  .endr

  // Second ROM entry point
  j _second_rom_start_boot
  .size _rom_interrupt_vector_asm, .-_rom_interrupt_vector_asm

// -----------------------------------------------------------------------------

  /**
   * Post C runtime initialization RISC-V vectored exception/interrupt handlers.
   */
  .balignl 256, UNIMP
  .global _rom_interrupt_vector_c
  .type _rom_interrupt_vector_c, @function
_rom_interrupt_vector_c:
  // Entry 0: exception handler.
  j rom_exception_handler

  // Entries 1-30: interrupt handlers.
  .rept 30
  j rom_interrupt_handler
  .endr

  // Entry 31: non-maskable interrupt handler.
  j rom_nmi_handler
  .size _rom_interrupt_vector_c, .-_rom_interrupt_vector_c

  // Pop ROM interrupt vector options.
  //
  // Re-enable compressed instructions, linker relaxation.
  .option pop

  /**
   * ROM shadow stack.
   */
  .section .bss
  .balignl 4, UNIMP
  .global _rom_shadow_stack
  .type _rom_shadow_stack, @object
_rom_shadow_stack:
  .zero 256 * 4
  .size _rom_shadow_stack, .-_rom_shadow_stack

// -----------------------------------------------------------------------------

/**
 * ROM runtime initialization code.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated executable space in ROM by the linker.
  .section .crt, "ax"

  // Linker relaxations are disabled until `gp` is set below, because otherwise
  // some sequences may be turned into `gp`-relative sequences, which is
  // incorrect when `gp` is not initialized.
  .option push
  .option norelax

  /**
   * Entry point after base ROM.
   */
  .balignl 4, UNIMP
  .global _second_rom_start_boot
  .type _second_rom_start_boot, @function
_second_rom_start_boot:
  // Set up the global pointer and re-enable linker relaxations.
  la gp, __global_pointer$
  .option pop

LABEL_FOR_TEST(kRomStartBootMaybeHalt)
  // Check if we should halt here.
  li   a0, (TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR + \
            OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET)
  lw   t0, OTP_CTRL_PARAM_CREATOR_SW_CFG_ROM_EXEC_EN_OFFSET(a0)
  bnez t0, .L_rma_spin_check_straps
LABEL_FOR_TEST(kRomStartBootHalted)
.L_halt_loop:
  wfi
  j .L_halt_loop

.L_rma_spin_check_straps:
  // Configure strap pins.
  //
  // | GPIO Pin:        | 24             | 23             | 22               |
  // |                  | (SW_STRAP_2)   | (SW_STRAP_1)   | (SW_STRAP_0)     |
  // |------------------+----------------+----------------+------------------|
  // | RMA Entry Value: | Strong pull-up | Strong pull-up | Strong pull-down |
  // |------------------+----------------+----------------+------------------|
  // | Configuration:   | Input          | Input          | Input            |
  // |                  | Pull-down      | Pull-down      | Pull-up          |
  li   a0, (TOP_DARJEELING_PINMUX_AON_BASE_ADDR + \
            PINMUX_MIO_PAD_ATTR_0_REG_OFFSET)
  li   t0, (1 << PINMUX_MIO_PAD_ATTR_0_PULL_EN_0_BIT) | \
           (1 << PINMUX_MIO_PAD_ATTR_0_PULL_SELECT_0_BIT)
  sw   t0, (SW_STRAP_0_PAD * 4)(a0)
  li   t0, (1 << PINMUX_MIO_PAD_ATTR_0_PULL_EN_0_BIT)
  sw   t0, (SW_STRAP_1_PAD * 4)(a0)
  sw   t0, (SW_STRAP_2_PAD * 4)(a0)
  li   a0, (TOP_DARJEELING_PINMUX_AON_BASE_ADDR + \
            PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET)

  // Spin for a minimum of 5us worth of cycles (assuming 100MHz clock), while we
  // wait for the RMA strap pull enables to propagate to the physical pads.
  csrw mcycle, zero
  li   t0, PINMUX_PAD_ATTR_PROP_CYCLES
.L_rma_strap_pu_spin_cycles_loop:
  csrr t1, mcycle
  bltu t1, t0, .L_rma_strap_pu_spin_cycles_loop

  // Read the strap GPIOs and check their value.
  li   a0, TOP_DARJEELING_GPIO_BASE_ADDR
  lw   t0, GPIO_DATA_IN_REG_OFFSET(a0)
  li   t5, SW_STRAP_MASK
  and  t0, t0, t5
  li   t4, (HARDENED_BOOL_TRUE ^ SW_STRAP_RMA_ENTRY)
  xor  t0, t0, t4
  bne  t0, t6, .L_clean_device_state

  // Double-check the GPIO strap value.
  li   t6, HARDENED_BOOL_TRUE
  li   a1, TOP_DARJEELING_GPIO_BASE_ADDR
  lw   t1, GPIO_DATA_IN_REG_OFFSET(a1)
  and  t1, t1, t5
  xor  t1, t1, t4
  beq  t1, t6, .L_clean_device_state
  unimp
  unimp
  unimp
  unimp

  // Spin for the OTP-specified number of cycles while we wait for
  // the lifecycle transition request on JTAG.  Since this is a wait
  // loop, disable the watchdog.
.L_rma_spin_init:
  csrw mcycle, zero
  li   a0, TOP_DARJEELING_AON_TIMER_AON_BASE_ADDR
  sw   zero, AON_TIMER_WDOG_CTRL_REG_OFFSET(a0)
.L_rma_spin_cycles_loop:
  li   a0, (TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR + \
            OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET)
  lw   t0, OTP_CTRL_PARAM_CREATOR_SW_CFG_RMA_SPIN_CYCLES_OFFSET(a0)
  csrr t1, mcycle
  bltu t1, t0, .L_rma_spin_cycles_loop
.L_rma_spin_lc_ctrl_loop:
  li   a0, TOP_DARJEELING_LC_CTRL_REGS_BASE_ADDR
  lw   t0, LC_CTRL_STATUS_REG_OFFSET(a0)
  andi t0, t0, (1 << LC_CTRL_STATUS_READY_BIT)
  beqz t0, .L_rma_spin_lc_ctrl_loop
  unimp
  unimp
  unimp
  unimp

.L_clean_device_state:
  /**
   * Clean Device State Part 1 (Please refer to `boot.md` section "Cleaning Device
   * State").
   */

  // Zero all writable registers except for `gp` (`x3`) since it's already initialized.
  li x1,  0x0
  li x2,  0x0
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

  // 2nd stage PMP setting
  // Reset ROM0 slots
  li   t0, 0
  csrw pmpaddr0, t0
  csrw pmpaddr1, t0
  csrw pmpaddr2, t0
  csrw pmpcfg0, t0
  // Update end of text region for ROM1
  la   t0, _epmp_second_text_tor_hi
  csrw pmpaddr5, t0

  /**
   * Setup C Runtime
   */

  // Initialize the `.bss` section.
  la   a0, _bss_start
  la   a1, _bss_end
  call crt_section_clear

  // Set up stack pointer.
  //
  // In RISC-V, the stack grows downwards, so we load the address of the highest
  // word in the stack into sp.
  //
  // If an exception fires, the handler is conventionally only allowed to clobber
  // memory at addresses below `sp`.
  la sp, _stack_end

  // Set up shadow stack pointer.
  //
  // The shadow stack, unlike the regular stack, grows upwards.
  la x18, _rom_shadow_stack


  // Set exception/interrupt handlers.
  //
  // Now that the C runtime is initialized it is safe to use C functions as
  // exception/interrupt handlers.
  //
  // Note: the increment just sets the low bits to 0b01 which is the vectored
  // mode setting.
  la   t0, (_rom_interrupt_vector_c + 1)
  csrw mtvec, t0

  /**
   * Jump to C Code
   */
  tail second_rom_main
  unimp
  unimp
  unimp
  unimp
  .size _second_rom_start_boot, .-_second_rom_start_boot
