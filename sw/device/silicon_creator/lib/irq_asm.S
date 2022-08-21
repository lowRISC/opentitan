// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/multibits_asm.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"
#include "flash_ctrl_regs.h"
#include "rstmgr_regs.h"

  // Place this code into the .crt section to be able to call it early in
  // the boot process before ePMP is reconfigured.
  //
  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated executable space in ROM by the linker.
  .section .crt, "ax"

  /**
   * Exception handler that is safe to call before the C runtime has been
   * initialized. It must not use the stack or global pointer.
   *
   * The exception handler will use the reset manager to trigger a reset.
   */
  .balign 4
  .global _asm_exception_handler
  .type _asm_exception_handler, @function
_asm_exception_handler:
.L_exception_loop:
  // Request a system reset.
  li t0, TOP_EARLGREY_RSTMGR_AON_BASE_ADDR
  li t1, MULTIBIT_ASM_BOOL4_TRUE
  sw t1, RSTMGR_RESET_REQ_REG_OFFSET(t0)

  // Disable access to flash.
  //
  // This is done after requesting a reset so that this function will
  // work even if it is in flash.
  li t0, TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR
  sw zero, FLASH_CTRL_DIS_REG_OFFSET(t0)

  wfi
  j   .L_exception_loop
  .size _asm_exception_handler, .-_asm_exception_handler
