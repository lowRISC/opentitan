// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// clkmgr interface to idle inputs. Uses the main clk @100MHz.

interface clkmgr_idle_if(input logic clk);
  import clkmgr_env_pkg::*;

  bit [NUM_TRANS-1:0] idle;

  function automatic void set_all_idle();
    idle = '1;
  endfunction

  function automatic void set_all_busy();
    idle = '0;
  endfunction

  function automatic void update(bit [NUM_TRANS-1:0] value);
    idle = value;
  endfunction

  function automatic void update_trans(input logic value, trans_e trans);
    idle[trans] = value;
  endfunction

  task automatic go_idle(trans_e trans, int cycles);
    if (!idle[trans]) begin
      repeat(cycles) @(negedge clk);
      idle[trans] = 1'b1;
    end
  endtask
endinterface
