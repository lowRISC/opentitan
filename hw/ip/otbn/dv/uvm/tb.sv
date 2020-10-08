// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages (test)
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import otbn_env_pkg::*;
  import otbn_test_pkg::*;

  // dep packages (rtl)
  import otbn_reg_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire idle, intr_done, intr_err;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if                    clk_rst_if (.clk(clk), .rst_n(rst_n));
  tl_if                         tl_if      (.clk(clk), .rst_n(rst_n));
  pins_if #(1)                  idle_if    (idle);
  pins_if #(NUM_MAX_INTERRUPTS) intr_if    (interrupts);
  assign interrupts[1:0] = {intr_err, intr_done};

  alert_esc_if alert_if[NumAlerts](.clk(clk), .rst_n(rst_n));
  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx;
  prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx;

  for (genvar k = 0; k < NumAlerts; k++) begin : connect_alerts_pins
    assign alert_rx[k] = alert_if[k].alert_rx;
    assign alert_if[k].alert_tx = alert_tx[k];
    initial begin
      uvm_config_db#(virtual alert_esc_if)::
        set(null, $sformatf("*.env.m_alert_agent_%0d", k), "vif", alert_if[k]);
    end
  end

  // dut
  otbn dut (
    .clk_i       (clk),
    .rst_ni      (rst_n),

    .tl_i        (tl_if.h2d),
    .tl_o        (tl_if.d2h),

    .idle_o      (idle),

    .intr_done_o (intr_done),
    .intr_err_o  (intr_err),

    .alert_rx_i  (alert_rx),
    .alert_tx_o  (alert_tx)

  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();

    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(idle_vif)::set(null, "*.env", "idle_vif", idle_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
