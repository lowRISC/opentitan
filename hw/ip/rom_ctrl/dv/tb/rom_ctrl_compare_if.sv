// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that is designed to be bound into rom_ctrl_compare. This can then look at internal
// information from the fsm and expose it cleanly. There are no ports: interactions with internal
// signals all work by upwards name references.

interface rom_ctrl_compare_if ();

  // Return whether the current FSM state is Waiting
  function automatic logic is_waiting();
    return u_compare.state_q == u_compare.Waiting;
  endfunction

  // Return the width of the addresses used in the compare module
  function automatic int unsigned get_AW();
    return u_compare.AW;
  endfunction

  // Return the top address used in the compare module (one less than the number of words in a
  // digest)
  function automatic int unsigned get_last_addr();
    return u_compare.LastAddr;
  endfunction

  // Force addr_q to the given value for a cycle, releasing the signal and returning on the next
  // negedge.
  task static force_addr_q(int unsigned value);
    force u_compare.addr_q = value;
    @(negedge u_compare.clk_i);
    release u_compare.addr_q;
  endtask

  // Override the FSM with an invalid state for a cycle, releasing the signal and returning on the
  // next negedge.
  task static splat_fsm_state();
    // Setting state_d directly is a bit fiddly because the enum type isn't in scope. But we know
    // that the valid states are separated by a hamming distance of at least 3, so we can just
    // invert one of the bits of the signal for a cycle and will know that we're setting an invalid
    // value.
    logic good_val;

    // Note that we have to set this separately from the declaration because it needs to be a static
    // variable in order to be used for the force statement below.
    good_val = u_compare.state_d[0];

    force u_compare.state_d[0] = ~good_val;
    @(negedge u_compare.clk_i);
    release u_compare.state_d[0];
  endtask

  // Override the next FSM state for a single cycle to be Done, releasing the signal and returning
  // on the next negedge.
  task static set_fsm_done();
    force u_compare.state_d = u_compare.Done;
    @(negedge u_compare.clk_i);
    release u_compare.state_d;
  endtask

  // Wait until addr_q becomes the given value, then return on the next negedge (mainly so that it's
  // easy to see what's going on in the waveforms)
  task automatic wait_addr_q(int unsigned value);
    wait(u_compare.addr_q == value);
    @(negedge u_compare.clk_i);
  endtask

endinterface
