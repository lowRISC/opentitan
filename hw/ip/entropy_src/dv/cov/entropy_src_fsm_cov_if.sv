// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Provides a window into the main_sm to help predict proper timing when trying to trigger
// particular state transitions.
interface entropy_src_fsm_cov_if
  import entropy_src_pkg::*;
  import prim_mubi_pkg::*;
  import entropy_src_main_sm_pkg::*;

(
  input wire clk_i,
  input state_e state_i
);

  state_e next_state;
  assign next_state = state_e'(state_i);

  // Sample the _next_ state (not the current state) of the main FSM, to allow VSeq's to fire an
  // enable or abort at the correct time to sample all FSM transitions
  clocking state_cb @(posedge clk_i);
    input next_state;
  endclocking

endinterface
