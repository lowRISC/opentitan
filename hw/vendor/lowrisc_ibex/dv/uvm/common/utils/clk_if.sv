// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//----------------------------- DESCRIPTION ------------------------------------
//
// Generic clock interface for clock events in various utilities
//
//------------------------------------------------------------------------------

interface clk_if(inout clk,
                 inout rst_n);

  logic clk_o;
  logic rst_no;

  clocking cb @(posedge clk);
  endclocking

  clocking cbn @(negedge clk);
  endclocking

  // Wait for 'n' clocks based of postive clock edge
  task automatic wait_clks(int num_clks);
    repeat (num_clks) @cb;
  endtask

  // Wait for 'n' clocks based of negative clock edge
  task automatic wait_n_clks(int num_clks);
    repeat (num_clks) @cbn;
  endtask

  // generate mid-test reset
  task automatic reset();
    rst_no = 1'b0;
    wait_clks(100);
    rst_no = 1'b1;
  endtask

  // generate clock
  initial begin
    clk_o = 1'b0;
    forever begin
      #10 clk_o = ~clk_o;
    end
  end

  // generate initial reset
  initial begin
    reset();
  end

  // Interface assignments
  assign clk = clk_o;
  assign rst_n = rst_no;

endinterface
