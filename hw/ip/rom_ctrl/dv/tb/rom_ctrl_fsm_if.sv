// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// rom_ctrl_fsm_if is designed to be instantiated inside a rom_ctrl_fsm_bound_if (which is
// responsible for comminucating with the design through upwards hierarchical references). This
// interface communicates with rom_ctrl_fsm_bound_if through its ports, described below.
//
// Because this interface is neither parameterised nor contains any upwards references, it is safe
// to use in an environment.

interface rom_ctrl_fsm_if (
  input logic      clk_i,
  input logic      rst_ni,

  rom_ctrl_pkg::fsm_state_e fsm_state_i,

  // The addr_q value in u_counter
  input bit [31:0] counter_addr_i,

  // The ports below give groups of signals to interact with a rom_ctrl_fsm_bound_if that contains
  // us. Describing the first group: when override_counter_o has a posedge, the rom_ctrl_bound_if
  // will start to force a signal in the design to match desired_counter_o. Once the force has
  // finished (maybe it takes a cycle, or maybe it was interrupted by a reset), the
  // rom_ctrl_bound_if will toggle the value of counter_o_overridden_i.
  //
  // The simpler groups ("force", not "override") are similar but the signal is forced to be true
  // for the period, rather than taking a value from an output port.

  output bit        override_counter_o,
  output bit [31:0] desired_counter_o,
  input bit         counter_o_overridden_i,

  output bit        override_addr_q_o,
  output bit [31:0] desired_addr_q_o,
  input bit         addr_q_overridden_i,

  output bit        override_select_bus_o,
  output bit [3:0]  desired_select_bus_o,
  input bit         select_bus_o_overridden_i,

  output bit        force_checker_done_o,
  input bit         checker_done_forced_i,

  output bit        force_counter_done_o,
  input bit         counter_done_forced_i,

  output bit        force_checker_start_o,
  input bit         checker_start_forced_i
);
  import uvm_pkg::*;

  // Return the current fsm state.
  function automatic rom_ctrl_pkg::fsm_state_e get_fsm_state();
    return fsm_state_i;
  endfunction

  // Wait until the FSM state is a value in the queue. Returns on the next negedge.
  task automatic wait_for_fsm_state_inside(rom_ctrl_pkg::fsm_state_e states_to_visit[$]);
    wait (fsm_state_i inside {states_to_visit});
    @(negedge clk_i);
  endtask

  // Wait until the FSM is no longer in the ReadingLow state. At this point, we've waited the bulk
  // of the time after reset and the dut is almost ready to start handling TL transactions. Returns
  // on the next negedge.
  task automatic wait_while_reading_low();
    wait (fsm_state_i != rom_ctrl_pkg::ReadingLow);
    @(negedge clk_i);
  endtask

  // Wait until the count in u_counter equals target and then return.
  task automatic wait_for_addr(int unsigned target);
    wait (counter_addr_i == target);
  endtask

  // Force the counter in u_counter to jump to the desired value on the next step (a posedge of the
  // clock when the go signal is asserted).
  //
  // To make the change easier to see in waves, we expect this task to be called at the negedge of
  // the clock (so addr_d changes at a surprising time) and will hold the forced signal until the
  // negedge after addr_q changes.
  //
  // If reset is applied, release the force and return immediately.
  task automatic force_addr(int unsigned desired);
    if (override_counter_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls to force_addr.")
    end

    desired_counter_o = desired;
    override_counter_o = 1;
    @(counter_o_overridden_i);
    override_counter_o = 0;
  endtask

  // Force the counter in u_counter to jump to the desired value on the next cycle (irrespective of
  // the "go" signal)
  //
  // To make the change easier to see in waves, we expect this task to be called at the negedge of
  // the clock (so addr_d changes at a surprising time) and will hold the forced signal until the
  // next negedge.
  //
  // If reset is applied, release the force and return immediately.
  task automatic force_addr_q(int unsigned desired);
    if (override_addr_q_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls to force_addr_q.")
    end

    desired_addr_q_o = desired;
    override_addr_q_o = 1;
    @(addr_q_overridden_i);
    override_addr_q_o = 0;
  endtask

  // Set rom_select_bus_o to the given value for a cycle. Returns on the next negedge.
  task static force_rom_select_bus_o(logic [3:0] value);
    if (override_select_bus_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls to force_rom_select_bus.")
    end

    desired_select_bus_o = value;
    override_select_bus_o = 1;
    @(select_bus_o_overridden_i);
    override_select_bus_o = 0;
  endtask

  // Force the checker_done signal to be true for a cycle. Returns on the next negedge.
  task static force_checker_done();
    if (force_checker_done_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls to force_checker_done.")
    end

    force_checker_done_o = 1;
    @(checker_done_forced_i);
    force_checker_done_o = 0;
  endtask

  // Force the counter_done signal to be true for a cycle. Returns on the next negedge.
  task static force_counter_done();
    if (force_counter_done_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls to force_counter_done.")
    end

    force_counter_done_o = 1;
    @(counter_done_forced_i);
    force_counter_done_o = 0;
  endtask

  // Force the start_checker_q signal for a cycle to start the checker. Returns on the next negedge.
  task static force_checker_start();
    if (force_checker_start_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls to force_checker_start.")
    end

    force_checker_start_o = 1;
    @(checker_start_forced_i);
    force_checker_start_o = 0;
  endtask

endinterface
