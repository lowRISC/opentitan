// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tb;

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import xbar_test_pkg::*;


  wire clk, rst_n;
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  wire tlul_assert_ctrl;
  pins_if #(1) tlul_assert_ctrl_if(tlul_assert_ctrl);

  xbar_main dut(
    .clk_main_i(clk),
    .rst_main_ni(rst_n),
    // TODO temp use same clk to avoid failure due to new feature (multi-clk #903)
    .clk_fixed_i(clk),
    .rst_fixed_ni(rst_n)
  );

  `include "xbar_tl_if_connection.sv"

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env*", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(tlul_assert_ctrl_vif)::set(null, "*.env", "tlul_assert_ctrl_vif",
                                              tlul_assert_ctrl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
