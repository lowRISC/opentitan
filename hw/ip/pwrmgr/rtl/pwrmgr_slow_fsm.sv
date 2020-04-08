// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager Slow FSM
//

`include "prim_assert.sv"

module pwrmgr_slow_fsm import pwrmgr_pkg::*; (
  input clk_i,
  input rst_ni,

  // sync'ed requests from peripherals
  input wakeup_i,
  input reset_req_i,

  // interface with fast fsm
  output logic req_pwrup_o,
  output pwrup_cause_e pwrup_cause_o,
  input ack_pwrup_i,
  input req_pwrdn_i,
  output logic ack_pwrdn_o,

  // low power entry configuration
  input main_pdb_i,
  input io_clk_en_i,
  input core_clk_en_i,

  // AST interface
  input pwr_ast_rsp_t ast_i,
  output pwr_ast_req_t ast_o
);

  assign req_pwrup_o = 1'b1;
  assign pwrup_cause_o = Por;

  // slow_clk_en should always be 1
  assign ast_o = '0;

  assign ack_pwrdn_o = 1'b1;


endmodule
