// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import rv_dm_env_pkg::*;
  import rv_dm_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  jtag_if jtag_if();

  `DV_ALERT_IF_CONNECT

  // dut
  rv_dm dut (
    .clk_i                (clk      ),
    .rst_ni               (rst_n    ),

    .tl_i                 (tl_if.h2d),
    .tl_o                 (tl_if.d2h),
    .alert_rx_i           (alert_rx ),
    .alert_tx_o           (alert_tx )
    // TODO: add remaining IOs and hook them
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual jtag_if)::set(null, "*.env.m_jtag_agent*", "vif", jtag_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
