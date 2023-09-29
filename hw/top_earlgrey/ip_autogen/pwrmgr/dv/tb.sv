// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import pwrmgr_env_pkg::*;
  import pwrmgr_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire clk_esc, rst_esc_n;
  wire clk_lc, rst_lc_n;
  wire clk_slow, rst_slow_n;
  wire devmode;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  clk_rst_if lc_clk_rst_if (
    .clk  (clk_lc),
    .rst_n(rst_lc_n)
  );
  clk_rst_if esc_clk_rst_if (
    .clk  (clk_esc),
    .rst_n(rst_esc_n)
  );
  clk_rst_if slow_clk_rst_if (
    .clk  (clk_slow),
    .rst_n(rst_slow_n)
  );
  pins_if #(NUM_MAX_INTERRUPTS) intr_if (interrupts);
  alert_esc_if esc_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  pins_if #(1) devmode_if (devmode);
  tl_if tl_if (
    .clk  (clk),
    .rst_n(rst_n)
  );

  assign interrupts[0] = pwrmgr_if.intr_wakeup;

  pwrmgr_if pwrmgr_if (
    .clk,
    .rst_n,
    .clk_slow,
    .rst_slow_n
  );

  `DV_ALERT_IF_CONNECT(clk_lc, rst_lc_n)

  // dut
  pwrmgr dut (
    .clk_i      (clk),
    .rst_ni     (rst_n),
    .clk_slow_i (clk_slow),
    .rst_slow_ni(rst_slow_n),
    .rst_main_ni(pwrmgr_if.rst_main_n),
    .clk_lc_i  (clk_lc),
    .rst_lc_ni (rst_lc_n),
    .clk_esc_i  (clk_esc),
    .rst_esc_ni (rst_esc_n),

    .tl_i(tl_if.h2d),
    .tl_o(tl_if.d2h),

    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx),

    .pwr_ast_i(pwrmgr_if.pwr_ast_rsp),
    .pwr_ast_o(pwrmgr_if.pwr_ast_req),

    .pwr_rst_i(pwrmgr_if.pwr_rst_rsp),
    .pwr_rst_o(pwrmgr_if.pwr_rst_req),

    .pwr_clk_i(pwrmgr_if.pwr_clk_rsp),
    .pwr_clk_o(pwrmgr_if.pwr_clk_req),

    .pwr_otp_i(pwrmgr_if.pwr_otp_rsp),
    .pwr_otp_o(pwrmgr_if.pwr_otp_req),

    .pwr_lc_i(pwrmgr_if.pwr_lc_rsp),
    .pwr_lc_o(pwrmgr_if.pwr_lc_req),

    .pwr_flash_i(pwrmgr_if.pwr_flash),
    .pwr_cpu_i  (pwrmgr_if.pwr_cpu),

    .fetch_en_o(pwrmgr_if.fetch_en),
    .wakeups_i (pwrmgr_if.wakeups_i),
    .rstreqs_i (pwrmgr_if.rstreqs_i),
    .ndmreset_req_i(pwrmgr_if.cpu_i.ndmreset_req),

    .lc_dft_en_i     (pwrmgr_if.lc_dft_en),
    .lc_hw_debug_en_i(pwrmgr_if.lc_hw_debug_en),

    .strap_o    (pwrmgr_if.strap),
    .low_power_o(pwrmgr_if.low_power),

    .rom_ctrl_i(pwrmgr_if.rom_ctrl),

    .sw_rst_req_i(pwrmgr_if.sw_rst_req_i),

    .esc_rst_tx_i(esc_if.esc_tx),
    .esc_rst_rx_o(esc_if.esc_rx),

    .intr_wakeup_o(pwrmgr_if.intr_wakeup)
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    esc_clk_rst_if.set_active();
    lc_clk_rst_if.set_active();
    slow_clk_rst_if.set_active();

    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "esc_clk_rst_vif", esc_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "lc_clk_rst_vif", lc_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "slow_clk_rst_vif", slow_clk_rst_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual alert_esc_if)::set(null, "*.env.m_esc_agent*", "vif", esc_if);
    uvm_config_db#(virtual pwrmgr_if)::set(null, "*.env", "pwrmgr_vif", pwrmgr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual pwrmgr_clock_enables_sva_if)::set(
        null, "*.env", "pwrmgr_clock_enables_sva_vif", dut.pwrmgr_clock_enables_sva_if);
    uvm_config_db#(virtual pwrmgr_rstmgr_sva_if)::set(null, "*.env", "pwrmgr_rstmgr_sva_vif",
                                                      dut.pwrmgr_rstmgr_sva_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end // initial begin

endmodule
