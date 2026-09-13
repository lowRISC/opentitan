// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for rv_timer TB. These properties tackle prim_intr_hw
// Intended to be used with a formal tool.

module rv_timer_interrupts_assert_fpv # (
  parameter int unsigned Width = 1,
  parameter bit          FlopOutput = 1,
  parameter              IntrT = "Event" // Event or Status
) (
  // event
  input  clk_i,
  input  rst_ni,
  input  [Width-1:0]  event_intr_i,

  // register interface
  input  [Width-1:0]  reg2hw_intr_enable_q_i,
  input  [Width-1:0]  reg2hw_intr_test_q_i,
  input               reg2hw_intr_test_qe_i,
  input  [Width-1:0]  reg2hw_intr_state_q_i,
  input               hw2reg_intr_state_de_o,
  input  [Width-1:0]  hw2reg_intr_state_d_o,

  // outgoing interrupt
  input logic [Width-1:0]  intr_o
);
  // internal signals from inputs to mirror DUT signals
  logic [Width-1:0] new_event;
  assign new_event = (({Width{reg2hw_intr_test_qe_i}} & reg2hw_intr_test_q_i) | event_intr_i);

  logic [Width-1:0] test_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) test_q <= '0;
    else if (reg2hw_intr_test_qe_i) test_q <= reg2hw_intr_test_q_i;
  end

  logic [Width-1:0] status;
  assign status = (IntrT == "Event") ? reg2hw_intr_state_q_i : (event_intr_i | test_q);

  // When state is event, make sure hw2reg_intr_state_de_o is only active when |new_event is high
  `ASSERT(IntrStateWriteEnableOnEvent_A, IntrT == "Event" |-> 
  (hw2reg_intr_state_de_o iff |new_event ))

  // Checks hw2reg_intr_state_d_o equals new_event OR'd with current interrupt state in Event mode
  `ASSERT(IntrStateOrUpdateOnEvent_A, IntrT == "Event" |-> 
  (hw2reg_intr_state_d_o == (new_event | reg2hw_intr_state_q_i)))

  // Check that in Status mode, hw2reg_intr_state_de_o is always driven high
  `ASSERT(IntrStateDeAlwaysOnStatus_A, IntrT == "Status" |-> hw2reg_intr_state_de_o)
  
  // Check hw2reg_intr_state_d_o reflects event | test_q in Status mode
  `ASSERT(IntrStateDataNewEventOrTestQ_A, IntrT == "Status" |-> 
  (hw2reg_intr_state_d_o == (event_intr_i | test_q)))

  // When FlopOutput == 1, intr_o is flopped status & reg2hw_intr_enable_q_i 
  `ASSERT(IntrOutgoingFlopped_A, FlopOutput == 1 |->
  (intr_o == $past(status & reg2hw_intr_enable_q_i)))

  // When FlopOutput == 0, intr_o is combinational reg2hw_intr_state_q_i & reg2hw_intr_enable_q_i 
  `ASSERT(IntrOutgoingNotFlopped_A, FlopOutput == 0 |->
  (intr_o == (reg2hw_intr_state_q_i & reg2hw_intr_enable_q_i)))

endmodule
