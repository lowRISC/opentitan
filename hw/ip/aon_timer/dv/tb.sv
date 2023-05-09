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

  wire                          clk, rst_n;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire                          clk_aon, rst_aon_n;
  wire                          lc_escalate_en_bit;
  lc_ctrl_pkg::lc_tx_t          lc_escalate_en;
  wire                          wkup_expired, wdog_bark, wdog_bark_nmi;
  wire                          wkup_req, rst_req;
  wire                          sleep;

  clk_rst_if fast_clk_rst_if(.clk(clk),     .rst_n(rst_n));
  clk_rst_if aon_clk_rst_if (.clk(clk_aon), .rst_n(rst_aon_n));

  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  // An input to the DUT that shows whether the CPU is enabled. Rather than wire up an interface
  // with an lc_tx_t member, we expose lc_escalate_en as a single bit and translate it to the right
  // type here.
  pins_if #(1) lc_escalate_en_if (lc_escalate_en_bit);
  assign lc_escalate_en = lc_escalate_en_bit ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off;

  // The interrupts that are in the fast clock domain
  pins_if #(NUM_MAX_INTERRUPTS) fast_intr_if(interrupts);
  assign interrupts[0] = wkup_expired;
  assign interrupts[1] = wdog_bark;

  // The interrupts in the slow clock domain
  pins_if #(2) aon_intr_if({wkup_req, rst_req});

  // An input to the DUT that shows whether we are in sleep mode
  pins_if #(1) sleep_if (sleep);

 `DV_ALERT_IF_CONNECT()

  aon_timer dut (
    .clk_i                     (clk),
    .rst_ni                    (rst_n),
    .clk_aon_i                 (clk_aon),
    .rst_aon_ni                (rst_aon_n),
    .tl_i                      (tl_if.h2d),
    .tl_o                      (tl_if.d2h),
    .alert_rx_i                (alert_rx),
    .alert_tx_o                (alert_tx),
    .lc_escalate_en_i          (lc_escalate_en),
    .intr_wkup_timer_expired_o (wkup_expired),
    .intr_wdog_timer_bark_o    (wdog_bark),
    .nmi_wdog_timer_bark_o     (wdog_bark_nmi),
    .wkup_req_o                (wkup_req),
    .aon_timer_rst_req_o       (rst_req),
    .sleep_mode_i              (sleep)
  );

  `ASSERT(wdog_bark_intr_is_nmi, wdog_bark === wdog_bark_nmi, clk, rst_n)

  initial begin
    // Configure interfaces
    fast_clk_rst_if.set_active();
    aon_clk_rst_if.set_active();
    aon_clk_rst_if.set_freq_khz(200);

    lc_escalate_en_if.drive_en('1);
    sleep_if.drive_en('1);

    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", fast_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "aon_clk_rst_vif", aon_clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);

    uvm_config_db#(virtual pins_if #(1))::set(null, "*.env", "lc_escalate_en_vif",
                                              lc_escalate_en_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", fast_intr_if);
    uvm_config_db#(virtual pins_if #(2))::set(null, "*.env", "aon_intr_vif", aon_intr_if);
    uvm_config_db#(virtual pins_if #(1))::set(null, "*.env", "sleep_vif", sleep_if);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
