// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_sparse_fsm_flop #(
  parameter type              StateEnumT = logic,
  parameter int               Width      = 1,
  parameter logic [Width-1:0] ResetValue = 0,
  // This should only be disabled in special circumstances, for example
  // in non-comportable IPs where an error does not trigger an alert.
  parameter bit               EnableAlertTriggerSVA = 1
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
    StateEnumT tmp = tmp.first;
    // An array to hold all possible enum values based on the given width.
    StateEnumT declared_fsms [2**Width];

    // Loop through all possible FSM values and store the listed StateEnumT enum value in
    // `declared_fsms`.
    // Ideally we can use `i < tmp.num`, but Xcelium does not support this syntax. (error msg:
    // Hierarchical name ('tmp.num()') not allowed within a constant expression)
    for (genvar i = 0; i < 2**Width; i++) begin : gen_declared_enum_list
      if (i == 0) assign declared_fsms[0] = tmp;
      else assign declared_fsms[i] = declared_fsms[i-1].next;
    end
    assign unused_valid_st = !(state_o inside {declared_fsms});
  `else
    assign unused_valid_st = 1'b1;
  `endif

  // If ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT is declared, the unused_assert_connected signal will
  // be set to 1 and the below check will pass.
  // If the assertion is not declared however, the statement below will fail.
  `ifdef INC_ASSERT
  logic unused_assert_connected;

  `ASSERT_INIT_NET(AssertConnected_A, unused_assert_connected === 1'b1 || !EnableAlertTriggerSVA)
  `endif

endmodule
