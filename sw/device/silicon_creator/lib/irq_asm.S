// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"
#include "aon_timer_regs.h"
#include "pwrmgr_regs.h"

  // This code is in the .crt section since it is designed to be safe
  // to run before the C runtime has been initialized.
  //
  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated executable space in ROM by the linker.
  .section .crt, "ax"

/**
 * Exception handler that is safe to call before the C runtime has been
 * initialized. It must not use the stack or global pointer.
 *
 * The exception handler will use the watchdog timer to trigger a reset.
 */
  .globl _asm_exception_handler
  .type _asm_exception_handler, @function
_asm_exception_handler:
  // Configure the power manager to enable resets.
  // Note: this enables all types of reset request for simplicity.
  li t0, TOP_EARLGREY_PWRMGR_AON_BASE_ADDR
  li t1, -1
  sw t1, PWRMGR_RESET_EN_REG_OFFSET(t0)

  // Trigger a configuration synchronization.
  li t1, (1 << PWRMGR_CFG_CDC_SYNC_SYNC_BIT)
  sw t1, PWRMGR_CFG_CDC_SYNC_REG_OFFSET(t0)

  // Set the watchdog bite threshold to 0 so that a reset will be
  // triggered immediately when the watchdog timer is enabled.
  li t0, TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR
  sw zero, AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET(t0)

  // Enable the watchdog timer (if it is not already enabled).
  li t1, (1 << AON_TIMER_WDOG_CTRL_ENABLE_BIT)
  sw t1, AON_TIMER_WDOG_CTRL_REG_OFFSET(t0)

  // Enter a wait for interrupt loop, the device should reset shortly.
.L_wfi_loop:
  wfi
  j   .L_wfi_loop

  // Set size so this function can be disassembled.
  .size _asm_exception_handler, .-_asm_exception_handler
