// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that is designed to be bound into rom_ctrl_fsm. This can then look at internal
// information from the fsm and expose it cleanly. There are no ports: interactions with internal
// signals all work by upwards name references.

interface rom_ctrl_fsm_if ();

  // Set rom_select_bus_o to the given value for a cycle. Returns on the next negedge.
  task static force_rom_select_bus_o(logic [3:0] value);
    force u_checker_fsm.rom_select_bus_o[3:0] = value;
    @(negedge u_checker_fsm.clk_i);
    release u_checker_fsm.rom_select_bus_o[3:0];
  endtask

  // Return the current fsm state.
  function automatic rom_ctrl_pkg::fsm_state_e get_fsm_state();
    return u_checker_fsm.state_q;
  endfunction

  // Wait until the FSM state is a value in the queue. Returns on the next negedge.
  task automatic wait_for_fsm_state_inside(rom_ctrl_pkg::fsm_state_e states_to_visit[$]);
    wait (u_checker_fsm.state_q inside {states_to_visit});
    @(negedge u_checker_fsm.clk_i);
  endtask

  // Force the checker_done signal to be true for a cycle. Returns on the next negedge.
  task static force_checker_done();
    force u_checker_fsm.checker_done = 1'b1;
    @(negedge u_checker_fsm.clk_i);
    release u_checker_fsm.checker_done;
  endtask

  // Force the counter_done signal to be true for a cycle. Returns on the next negedge.
  task static force_counter_done();
    force u_checker_fsm.counter_done = 1'b1;
    @(negedge u_checker_fsm.clk_i);
    release u_checker_fsm.counter_done;
  endtask

  // Force the start_checker_q signal for a cycle to start the checker. Returns on the next negedge.
  task static force_checker_start();
    force u_checker_fsm.start_checker_q = 1'b1;
    @(negedge u_checker_fsm.clk_i);
    release u_checker_fsm.start_checker_q;
  endtask

  // Force the address in the counter submodule (which is supposed to choose which address to read
  // next) to the given value for one cycle. Returns on the next negedge.
  task static force_counter_addr(int unsigned addr);
    force u_checker_fsm.u_counter.addr_q = addr;
    @(negedge u_checker_fsm.clk_i);
    release u_checker_fsm.u_counter.addr_q;
  endtask

  // Wait until the FSM is no longer in the ReadingLow state. At this point, we've waited the bulk
  // of the time after reset and the dut is almost ready to start handling TL transactions. Returns
  // on the next negedge.
  task automatic wait_while_reading_low();
    wait (u_checker_fsm.state_q != rom_ctrl_pkg::ReadingLow);
    @(negedge u_checker_fsm.clk_i);
  endtask

endinterface
