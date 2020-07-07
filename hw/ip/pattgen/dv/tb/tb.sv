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

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire cio_pda0_tx_o;
  wire cio_pda0_tx_en_o;
  wire cio_pcl0_tx_o;
  wire cio_pcl0_tx_en_o;

  wire cio_pda1_tx_o;
  wire cio_pda1_tx_en_o;
  wire cio_pcl1_tx_o;
  wire cio_pcl1_tx_en_o;


  wire intr_patt_done0;
  wire intr_patt_done1;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk_i), .rst_n(rst_ni));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);

  tl_if tl_if(.clk(clk_i), .rst_n(rst_ni));

  // dut
  pattgen dut (
    .clk_i                (clk       ),
    .rst_ni               (rst_n     ),

    .tl_i                 (tl_if.h2d ),
    .tl_o                 (tl_if.d2h ),

    .cio_pda0_tx_o        (cio_pda0_tx_o     ),
    .cio_pda0_tx_en_o     (cio_pda0_tx_en_o  ),
    .cio_pcl0_tx_o        (cio_pcl0_tx_o     ),
    .cio_pcl0_tx_en_o     (cio_pcl0_tx_en_o  ),

    .cio_pda1_tx_o        (cio_pda1_tx_o     ),
    .cio_pda1_tx_en_o     (cio_pda1_tx_en_o  ),
    .cio_pcl1_tx_o        (cio_pcl1_tx_o     ),
    .cio_pcl1_tx_en_o     (cio_pcl1_tx_en_o  ),

    .intr_patt_done0_o    (intr_patt_done0 ),
    .intr_patt_done1_o    (intr_patt_done1 )
  );

  // interrupt
  assign interrupts[PattDone0]   = intr_patt_done0;
  assign interrupts[PattDone1]   = intr_patt_done1;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule : tb
