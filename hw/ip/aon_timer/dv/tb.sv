// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import aon_timer_env_pkg::*;
  import aon_timer_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  logic rst_aon_n_gen;
  wire rst_aon_n;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  clk_rst_if clk_aon_rst_if(.clk(clk_aon), .rst_n(rst_aon_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  // dut
  aon_timer dut (
    .clk_i                     (clk      ),
    .rst_ni                    (rst_n    ),
    .clk_aon_i                 (clk_aon  ),
    .rst_aon_ni                (rst_aon_n),
    .tl_i                      (tl_if.h2d),
    .tl_o                      (tl_if.d2h),
    .lc_cpu_en_i               (lc_ctrl_pkg::Off),
    .intr_wkup_timer_expired_o (),
    .intr_wdog_timer_bark_o    (),
    .aon_timer_wkup_req_o      (),
    .aon_timer_rst_req_o       (),
    .sleep_mode_i              ('0)
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_aon_rst_if.set_active();
    clk_rst_if.set_active();
    clk_aon_rst_if.set_freq_khz(200);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_aon_rst_vif", clk_aon_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
