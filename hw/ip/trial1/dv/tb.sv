// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tb;

  import tlul_pkg::*;
  import trial1_reg_pkg::*;

  // Clock gen
  logic clk, rst_n;
  parameter time CLK_PERIOD = 10ns;
  initial begin
    clk = 0;
    forever begin
      #(CLK_PERIOD/2) clk = ~clk;
    end
  end
  // Reset gen
  initial begin
    rst_n = 1'b1;
    #(CLK_PERIOD/2.5) rst_n = 1'b0;
    #(CLK_PERIOD*4) rst_n = 1'b1;
    repeat(10000)
      @(posedge clk);
    $finish;
  end

  // BUS interface
  tl_h2d_t tl_h2d;
  tl_d2h_t tl_d2h;

  //logic bus_reg_valid;
  //logic bus_reg_ready;
  //bus_reg_t bus_reg;

  //logic reg_bus_valid;
  //logic reg_bus_ready;
  //reg_bus_t reg_bus;

  // auto generated signals to/from reg/hw
  trial1_hw2reg_t hw2reg;
  trial1_reg2hw_t reg2hw;

  trial1_reg_top dut (
    .clk_i  (clk),
    .rst_ni (rst_n),

    .tl_i   (tl_h2d),
    .tl_o   (tl_d2h),
    //.bus_reg_valid,
    //.bus_reg_ready,
    //.bus_reg,

    //.reg_bus_valid,
    //.reg_bus_ready,
    //.reg_bus,

    .reg2hw,
    .hw2reg
  );

  trial1_test test (
    .clk,
    .rst_n,

    .tl_h2d   (tl_h2d),
    .tl_d2h   (tl_d2h),
    //.bus_reg_valid,
    //.bus_reg_ready,
    //.bus_reg,

    //.reg_bus_valid,
    //.reg_bus_ready,
    //.reg_bus,

    .reg2hw,
    .hw2reg
  );

endmodule
