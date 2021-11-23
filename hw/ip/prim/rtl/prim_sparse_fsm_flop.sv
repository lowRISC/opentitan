// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_sparse_fsm_flop #(
  parameter type              StateEnumT = logic,
  parameter int               Width      = 1,
  parameter logic [Width-1:0] ResetValue = 0
) (
  input                    clk_i,
  input                    rst_ni,
  input        [Width-1:0] state_i,
  output logic [Width-1:0] state_o
);

  logic unused_valid_st;

  prim_flop #(
    .Width(Width),
    .ResetValue(ResetValue)
  ) u_state_flop (
    .clk_i,
    .rst_ni,
    .d_i(state_i),
    .q_o(state_o)
  );

  `ifdef INC_ASSERT
    StateEnumT tmp;
    assign unused_valid_st = $cast(tmp, state_o);
  `else
    assign unused_valid_st = 1'b1;
  `endif

  // If ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT is declared, the unused_assert_connected signal will
  // be set to 1 and the below check will pass.
  // If the assertion is not declared however, the statement below will fail.
  `ifdef INC_ASSERT
  logic unused_assert_connected;

  // ASSERT_INIT can only be used for paramters/constants in FPV.
  `ifdef SIMULATION
  `ASSERT_INIT(AssertConnected_A, unused_assert_connected === 1'b1)
  `endif
  `endif

endmodule

`define ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, MAX_CYCLES_ = 5) \
  `ASSERT(NAME_, $fell(PRIM_HIER_.unused_valid_st) |-> ##[1:MAX_CYCLES_] $rose(ALERT_.alert_p)) \
  `ifdef INC_ASSERT \
  assign PRIM_HIER_.unused_assert_connected = 1'b1; \
  `endif
