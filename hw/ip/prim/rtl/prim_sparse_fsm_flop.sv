// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_sparse_fsm_flop #(
  parameter int               Width      = 1,
  parameter type              StateEnumT = logic [Width-1:0],
  parameter logic [Width-1:0] ResetValue = '0,
  // This should only be disabled in special circumstances, for example
  // in non-comportable IPs where an error does not trigger an alert.
  parameter bit               EnableAlertTriggerSVA = 1
`ifdef SIMULATION
  ,
  // In case this parameter is set to a non-empty string, the
  // prim_sparse_fsm_flop_if will also force the signal with this name
  // in the parent module that instantiates prim_sparse_fsm_flop.
  parameter string            CustomForceName = ""
`endif
) (
  input             clk_i,
  input             rst_ni,
  input  StateEnumT state_i,
  output StateEnumT state_o
);

  logic unused_err_o;

  logic [Width-1:0] state_raw;
  prim_flop #(
    .Width(Width),
    .ResetValue(ResetValue)
  ) u_state_flop (
    .clk_i,
    .rst_ni,
    .d_i(state_i),
    .q_o(state_raw)
  );
  assign state_o = StateEnumT'(state_raw);

  `ifdef INC_ASSERT
  assign unused_err_o = is_undefined_state(state_o);

  function automatic logic is_undefined_state(StateEnumT sig);
    // This is written with a vector in order to make it amenable to x-prop analysis.
    logic is_defined = 1'b0;
    for (int i = 0, StateEnumT t = t.first(); i < t.num(); i += 1, t = t.next()) begin
      is_defined |= (sig === t);
    end
    return ~is_defined;
  endfunction

  `else
    assign unused_err_o = 1'b0;
  `endif

  // If ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT is declared, the unused_assert_connected signal will
  // be set to 1 and the below check will pass.
  // If the assertion is not declared however, the statement below will fail.
  `ifdef INC_ASSERT
  logic unused_assert_connected;

  `ASSERT_INIT_NET(AssertConnected_A, unused_assert_connected === 1'b1 || !EnableAlertTriggerSVA)
  `endif

endmodule
