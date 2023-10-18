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
#include "rstmgr_regs.h"
#include "rv_core_ibex_regs.h"
#include "sensor_ctrl_regs.h"
#include "sram_ctrl_regs.h"

// This macro defines convenience labels for tests that use a debugger.
#define LABEL_FOR_TEST(kName_) .local kName_ ; kName_: ;

.equ UNIMP, 0xc0001073
// We will configure the watchdog timers to reset the chip in the event that the
// ROM stalls. The watchdog's bite and bark thresholds are set to 1 and 1.125
// seconds, respectively, assuming a clock frequency of 62.5 MHz.
.equ WDOG_BITE_THOLD, 62500000
.equ WDOG_BARK_THOLD, WDOG_BITE_THOLD * 9 / 8

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

  // Ibex Reset Handler:
  j _rom_start_boot
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
   * Entry point after reset.
   */
  .balignl 4, UNIMP
  .global _rom_start_boot
  .type _rom_start_boot, @function
_rom_start_boot:
  // Set up the global pointer and re-enable linker relaxations.
  la gp, __global_pointer$
  .option pop

LABEL_FOR_TEST(kRomStartBootMaybeHalt)
  // Check if we should halt here.
  li   a0, (TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR + \
            OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET)
  lw   t0, OTP_CTRL_PARAM_CREATOR_SW_CFG_ROM_EXEC_EN_OFFSET(a0)
  bnez t0, .L_exec_en
LABEL_FOR_TEST(kRomStartBootHalted)
.L_halt_loop:
  wfi
  j .L_halt_loop

LABEL_FOR_TEST(kRomStartBootExecEn)
.L_exec_en:
  // Enable NMIs from the watchdog timer.
  li t0, TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR
  li t1, (1 << RV_CORE_IBEX_NMI_ENABLE_WDOG_EN_BIT)
  sw t1, RV_CORE_IBEX_NMI_ENABLE_REG_OFFSET(t0)

  // Configure the power manager to enable resets.
  // Note: this enables all types of reset request for simplicity.
  li t0, TOP_DARJEELING_PWRMGR_AON_BASE_ADDR
  li t1, -1
  sw t1, PWRMGR_RESET_EN_REG_OFFSET(t0)

  // Trigger a power manager configuration synchronization.
  li t1, (1 << PWRMGR_CFG_CDC_SYNC_SYNC_BIT)
  sw t1, PWRMGR_CFG_CDC_SYNC_REG_OFFSET(t0)

  // Configure the watchdog's bark and bite thresholds.
  li t0, TOP_DARJEELING_AON_TIMER_AON_BASE_ADDR
  li t1, WDOG_BARK_THOLD
  sw t1, AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET(t0)
  li t1, WDOG_BITE_THOLD
LABEL_FOR_TEST(kRomStartStoreT1ToBiteThold)
  sw t1, AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET(t0)

  // Enable the watchdog timer.
  li t1, (1 << AON_TIMER_WDOG_CTRL_ENABLE_BIT)
  sw t1, AON_TIMER_WDOG_CTRL_REG_OFFSET(t0)

  // Configure rstmgr alert and cpu info collection.
  li   a0, (TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR + \
            OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET)
  lw   t0, OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_RSTMGR_INFO_EN_OFFSET(a0)
  li   t1, HARDENED_BYTE_BOOL_TRUE
  li   a0, TOP_DARJEELING_RSTMGR_AON_BASE_ADDR
  // Enable alert info collection if enabled in OTP.
  andi t2, t0, 0xff
  bne  t2, t1, .L_skip_rstmgr_alert_info_en
  li   t2, (1 << RSTMGR_ALERT_INFO_CTRL_EN_BIT)
  sw   t2,  RSTMGR_ALERT_INFO_CTRL_REG_OFFSET(a0)
.L_skip_rstmgr_alert_info_en:
  // Enable cpu info collection if enabled in OTP.
  srli t0, t0, 8
  andi t2, t0, 0xff
  bne  t2, t1, .L_skip_rstmgr_cpu_info_en
  li   t2, (1 << RSTMGR_CPU_INFO_CTRL_EN_BIT)
  sw   t2,  RSTMGR_ALERT_INFO_CTRL_REG_OFFSET(a0)
.L_skip_rstmgr_cpu_info_en:

LABEL_FOR_TEST(kRomStartWatchdogEnabled)
  // Clear all the machine-defined interrupts, `MEIE`, `MTIE`, and `MSIE` fields
  // of `mie`.
  li   t0, 0x00000888
  csrc mie, t0

  // Check if AST initialization should be skipped.
  li   a0, (TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR + \
            OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET)
  lw   t0, OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_INIT_EN_OFFSET(a0)
  li   t1, MULTIBIT_ASM_BOOL4_TRUE
  bne  t0, t1, .L_entropy_enable

  // Copy the AST configuration from OTP.
  li   a0, (TOP_DARJEELING_AST_BASE_ADDR)
  li   a1, (TOP_DARJEELING_AST_BASE_ADDR + AST_REGAL_REG_OFFSET + 4)
  li   a2, (TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR + \
            OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET + \
            OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_CFG_OFFSET)
  call crt_section_copy

  // Enable jittery clock if enabled in OTP.
  li   a0, (TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR + \
            OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET)
  lw   t0, OTP_CTRL_PARAM_CREATOR_SW_CFG_JITTER_EN_OFFSET(a0)
  li   a0, TOP_DARJEELING_CLKMGR_AON_BASE_ADDR
  sw   t0, CLKMGR_JITTER_ENABLE_REG_OFFSET(a0)

.L_entropy_enable:
  // The following sequence enables the minimum level of entropy required to
  // initialize memory scrambling, as well as the entropy distribution network.
  li a0, TOP_DARJEELING_CSRNG_BASE_ADDR
  li t0, (MULTIBIT_ASM_BOOL4_TRUE << CSRNG_CTRL_ENABLE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_TRUE << CSRNG_CTRL_SW_APP_ENABLE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_TRUE << CSRNG_CTRL_READ_INT_STATE_OFFSET)
  sw t0, CSRNG_CTRL_REG_OFFSET(a0)

  li a0, TOP_DARJEELING_EDN0_BASE_ADDR
  li t0, (MULTIBIT_ASM_BOOL4_TRUE << EDN_CTRL_EDN_ENABLE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_TRUE << EDN_CTRL_BOOT_REQ_MODE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_FALSE << EDN_CTRL_AUTO_REQ_MODE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_FALSE << EDN_CTRL_CMD_FIFO_RST_OFFSET)
  sw t0, EDN_CTRL_REG_OFFSET(a0)

  // Scramble and initialize main memory (main SRAM).
  // Memory accesses will stall until initialization is complete.
  // Set `SRAM_KEY_RENEW_EN` OTP item to `HARDENED_BOOL_FALSE` to disable and
  // any other value to enable.
  li   a0, (TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR + \
            OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET)
  lw   t0, OTP_CTRL_PARAM_CREATOR_SW_CFG_SRAM_KEY_RENEW_EN_OFFSET(a0)
  li   t1, HARDENED_BOOL_FALSE
  beq t0, t1, .L_sram_key_renew_skip
  li a0, TOP_DARJEELING_SRAM_CTRL_MAIN_REGS_BASE_ADDR
  li a1, (1 << SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT) | (1 << SRAM_CTRL_CTRL_INIT_BIT)
  sw a1, SRAM_CTRL_CTRL_REG_OFFSET(a0)
.L_sram_key_renew_skip:

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

  // Must be called prior to any Main RAM access.
  call base_rom_epmp_init

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
  tail base_rom_main
  unimp
  unimp
  unimp
  unimp
  .size _rom_start_boot, .-_rom_start_boot
