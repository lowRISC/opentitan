// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that is designed to be instantiated inside a rom_ctrl_compare_bound_if, which is
// itself bound into a rom_ctrl_compare instance called u_compare and handles the communication
// between this interface (which is not parameterised) and the design (which is).

interface rom_ctrl_compare_if (
  input wire        clk_i,
  input wire        rst_ni,

  // The AW and LastAddr parameters
  input bit [31:0]  param_AW_i,
  input bit [31:0]  param_LastAddr_i,

  // The Waiting and Done enum values used by the state_q signal in the compare FSM.
  input logic [4:0] param_Waiting_i,
  input logic [4:0] param_Done_i,

  // The current value of the design's addr_q signal is in addr_q_i. If force_addr_q_o is set then
  // addr_q in the design will be forced to equal (the bottom AW bits of) desired_addr_q_o.
  input wire [31:0] addr_q_i,
  output bit        force_addr_q_o,
  output bit [31:0] desired_addr_q_o,

  // The current value of the design's state_d and state_q signals are in state_d_i and state_q_i.
  // If force_state_d_o is set then state_d in the design will be forced to equal desired_state_d_o.
  input logic [4:0] state_q_i,
  input logic [4:0] state_d_i,
  output bit        force_state_d_o,
  output bit [4:0]  desired_state_d_o
);
  import uvm_pkg::*;

  // Wait until the next negedge of clk_i, returning early if rst_ni becomes false.
  task automatic wait_clk_n_or_rst();
    fork : isolation_fork begin
      fork
        @(negedge clk_i);
        wait(!rst_ni);
      join_any
      disable fork;
    end join
  endtask

  // Return whether the current FSM state is Waiting
  function automatic logic is_waiting();
    return state_q_i == param_Waiting_i;
  endfunction

  // Return the width of the addresses used in the compare module
  function automatic int unsigned get_AW();
    return param_AW_i;
  endfunction

  // Return the top address used in the compare module (one less than the number of words in a
  // digest)
  function automatic int unsigned get_last_addr();
    return param_LastAddr_i;
  endfunction

  // Force addr_q to the given value for a cycle, releasing the signal and returning on the next
  // negedge.
  task automatic force_addr_q(int unsigned value);
    if (force_addr_q_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls that force addr_q.")
    end

    desired_addr_q_o = value;
    force_addr_q_o = 1;
    wait_clk_n_or_rst();
    force_addr_q_o = 0;

    // Dropping force_addr_q_o will cause rom_ctrl_bound_if to release the force on addr_q. To avoid
    // any overlaps, wait until that has happened before returning from this task.
    //
    // The wait_clk_n_or_rst() that has just finished triggers in the Active region. Adding a #0;
    // delay here will postpone this task to the Inactive region, which will happen after the bound
    // interface sees force_addr_q_o drop and releases addr_q.
    #0;
  endtask

  // Wait until addr_q becomes the given value, then return on the next negedge or reset (mainly so
  // that it's easy to see what's going on in the waveforms)
  task automatic wait_addr_q(int unsigned value);
    wait(addr_q_i == value);
    wait_clk_n_or_rst();
  endtask

  // Override the FSM's state_d for a single cycle, releasing the signal and returning on the next
  // negedge.
  task automatic force_fsm_state_d(bit [4:0] desired_state_d);
    if (force_state_d_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls to force_fsm_state_d.")
    end

    desired_state_d_o = desired_state_d;
    force_state_d_o = 1;
    wait_clk_n_or_rst();
    force_state_d_o = 0;
  endtask

  // Jump the FSM to an invalid state by forcing state_d a cycle, releasing the signal and returning
  // on the next negedge.
  task automatic splat_fsm_state();
    // Since the valid states are separated by a hamming distance of at least 3, we can just invert
    // one of the bits of the signal for a cycle and will know that we're setting an invalid value.
    force_fsm_state_d(state_d_i ^ 5'b00001);
  endtask

  // Override the next FSM state for a single cycle to be Done, releasing the signal and returning
  // on the next negedge.
  task automatic set_fsm_done();
    force_fsm_state_d(param_Done_i);
  endtask

endinterface
