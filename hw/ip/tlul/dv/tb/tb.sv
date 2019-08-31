// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tb;

  import uvm_pkg::*;

  logic clk;
  logic rst_n;

  tlul_xbar dut(
    .clk_i(clk),
    .rst_ni(rst_n)
  );

  `include "tl_if_connect_macros.svh"
  `include "xbar_tl_if_connection.sv"

  clk_if xbar_clk_if(.clk(clk));

  initial begin
    uvm_config_db#(virtual clk_if)::set(null, "*", "clk_if", xbar_clk_if);
    run_test();
  end

  // Generate clk
  initial begin
    clk = 1'b0;
    forever begin
      #10 clk = ~clk;
    end
  end

  // Generate reset
  initial begin
    rst_n = 1'b0;
    repeat(100) @(posedge clk);
    rst_n = 1'b1;
  end

endmodule
