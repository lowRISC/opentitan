// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module aes_idle_check
  import aes_reg_pkg::*;
(
 input logic               clk_i,
 input logic               rst_ni,
 input aes_reg2hw_t        reg2hw,
 input prim_mubi_pkg::mubi4_t idle_i
 );


  logic                    is_running;
  logic                    idle;

  assign idle = (reg2hw.status.idle.q == 1'b1);

  // make sure idle_i always matched the register idle state
  `ASSERT(IdleNotIdle_A, prim_mubi_pkg::mubi4_bool_to_mubi(idle) == idle_i)
endmodule
