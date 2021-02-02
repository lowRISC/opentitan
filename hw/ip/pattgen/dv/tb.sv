// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import pattgen_env_pkg::*;
  import pattgen_test_pkg::*;
  import pattgen_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;

  wire [NUM_PATTGEN_CHANNELS-1:0] pda_tx_o;
  wire [NUM_PATTGEN_CHANNELS-1:0] pcl_tx_o;
  wire intr_done_ch0;
  wire intr_done_ch1;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  pattgen_if #(NUM_PATTGEN_CHANNELS) pattgen_if();
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  // dut
  pattgen dut (
    .clk_i                (clk           ),
    .rst_ni               (rst_n         ),

    .tl_i                 (tl_if.h2d     ),
    .tl_o                 (tl_if.d2h     ),

    .cio_pda0_tx_o        (pda_tx_o[0]   ),
    .cio_pcl0_tx_o        (pcl_tx_o[0]   ),
    .cio_pda1_tx_o        (pda_tx_o[1]   ),
    .cio_pcl1_tx_o        (pcl_tx_o[1]   ),
    .intr_done_ch0_o      (intr_done_ch0 ),
    .intr_done_ch1_o      (intr_done_ch1 )
  );

  assign pattgen_if.rst_ni   = rst_n;
  assign pattgen_if.clk_i    = clk;
  assign pattgen_if.pda_tx   = pda_tx_o;
  assign pattgen_if.pcl_tx   = pcl_tx_o;

  assign interrupts[DoneCh0] = intr_done_ch0;
  assign interrupts[DoneCh1] = intr_done_ch1;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual pattgen_if)::set(null, "*.env.m_pattgen_agent*", "vif", pattgen_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
