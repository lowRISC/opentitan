// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// This module uses bind to hook-up the timer core and interrupt FPV properties
// for formal verification

module rv_timer_bind_fpv;

  bind timer_core rv_timer_core_assert_fpv#(.N(1)) i_rv_timer_core_assert_fpv       (.*);
  bind prim_intr_hw rv_timer_interrupts_assert_fpv i_rv_timer_interrupts_assert_fpv (.*);

endmodule: rv_timer_bind_fpv
