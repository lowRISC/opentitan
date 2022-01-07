// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import sysrst_ctrl_env_pkg::*;
  import sysrst_ctrl_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire clk_aon, rst_aon_n;

  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  clk_rst_if clk_aon_rst_if (
    .clk  (clk_aon),
    .rst_n(rst_aon_n)
  );
  pins_if #(NUM_MAX_INTERRUPTS) intr_if (interrupts);
  pins_if #(1) devmode_if (devmode);
  tl_if tl_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  sysrst_ctrl_if sysrst_ctrl_if (
    .clk_i (clk_aon),
    .rst_ni(rst_aon_n)
  );

  `DV_ALERT_IF_CONNECT

  // dut
  sysrst_ctrl dut (
    .clk_i            (clk),
    .rst_ni           (rst_n),
    .clk_aon_i        (clk_aon),
    .rst_aon_ni       (rst_aon_n),
    .tl_i             (tl_if.h2d),
    .tl_o             (tl_if.d2h),
    .alert_rx_i       (alert_rx),
    .alert_tx_o       (alert_tx),
    .cio_ac_present_i (sysrst_ctrl_if.ac_present),
    .cio_ec_rst_l_i   (sysrst_ctrl_if.ec_rst_l_in),
    .cio_flash_wp_l_i (sysrst_ctrl_if.flash_wp_l_in),
    .cio_key0_in_i    (sysrst_ctrl_if.key0_in),
    .cio_key1_in_i    (sysrst_ctrl_if.key1_in),
    .cio_key2_in_i    (sysrst_ctrl_if.key2_in),
    .cio_pwrb_in_i    (sysrst_ctrl_if.pwrb_in),
    .cio_lid_open_i   (sysrst_ctrl_if.lid_open),
    .cio_bat_disable_o(sysrst_ctrl_if.bat_disable),
    .cio_flash_wp_l_o (sysrst_ctrl_if.flash_wp_l),
    .cio_ec_rst_l_o   (sysrst_ctrl_if.ec_rst_l_out),
    .cio_key0_out_o   (sysrst_ctrl_if.key0_out),
    .cio_key1_out_o   (sysrst_ctrl_if.key1_out),
    .cio_key2_out_o   (sysrst_ctrl_if.key2_out),
    .cio_pwrb_out_o   (sysrst_ctrl_if.pwrb_out),
    .cio_z3_wakeup_o  (sysrst_ctrl_if.z3_wakeup)
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    clk_aon_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_aon_rst_vif", clk_aon_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual sysrst_ctrl_if)::set(null, "*.env", "vif", sysrst_ctrl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  `ASSERT(CheckFlashWrProtRst, !rst_aon_n -> sysrst_ctrl_if.flash_wp_l == 0, clk_aon, 0)
  `ASSERT(CheckEcPwrOnRst, !rst_aon_n -> sysrst_ctrl_if.ec_rst_l_out == 0, clk_aon, 0)

endmodule
