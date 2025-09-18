// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"
#include "rv_core_ibex_regs.h"

// This code can be used as the ROM in test environments to exit immediately.

  .balign 4
  .global _reset_start
  .type _reset_start, @function
_reset_start:

// Write exit code 0 to `rv_core_ibex.dv_sim_window[0]` (exit status register).
li a0, TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR
li a1, 0x900d
sw a1, RV_CORE_IBEX_DV_SIM_WINDOW_REG_OFFSET(a0)

// Wait for shutdown.
wfi
