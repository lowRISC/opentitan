// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef __CIP_MACROS_SVH__
`define __CIP_MACROS_SVH__

// Declare array of alert interface, using parameter NUM_ALERTS and LIST_OF_ALERTS, and connect to
// arrays of wires (alert_tx and alert_rx). User need to manually connect these wires to DUT
// Also set each alert_if to uvm_config_db to use in env
`ifndef DV_ALERT_IF_CONNECT
`define DV_ALERT_IF_CONNECT \
  alert_esc_if alert_if[NUM_ALERTS](.clk(clk), .rst_n(rst_n)); \
  prim_alert_pkg::alert_rx_t [NUM_ALERTS-1:0] alert_rx; \
  prim_alert_pkg::alert_tx_t [NUM_ALERTS-1:0] alert_tx; \
  for (genvar k = 0; k < NUM_ALERTS; k++) begin : connect_alerts_pins \
    assign alert_rx[k] = alert_if[k].alert_rx; \
    assign alert_if[k].alert_tx = alert_tx[k]; \
    initial begin \
      uvm_config_db#(virtual alert_esc_if)::set(null, $sformatf("*.env.m_alert_agent_%0s", \
          LIST_OF_ALERTS[k]), "vif", alert_if[k]); \
    end \
  end
`endif

// Declare edn clock, reset and push_pull_if. Connect them and set edn_clk_rst_if and edn_if for
// using them in env
// Use this macro in tb.sv if the IP connects to a EDN interface
// TODO, tie core reset with EDN reset for now
`ifndef DV_EDN_IF_CONNECT
`define DV_EDN_IF_CONNECT \
  wire edn_rst_n = rst_n; \
  wire edn_clk; \
  clk_rst_if edn_clk_rst_if(.clk(edn_clk), .rst_n(edn_rst_n)); \
  push_pull_if #(.DeviceDataWidth(cip_base_pkg::EDN_DATA_WIDTH)) edn_if(.clk(edn_clk), \
                                                                        .rst_n(edn_rst_n)); \
  initial begin \
    edn_clk_rst_if.set_active(.drive_rst_n_val(0)); \
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "edn_clk_rst_vif", edn_clk_rst_if); \
    uvm_config_db#(virtual push_pull_if#(.DeviceDataWidth(cip_base_pkg::EDN_DATA_WIDTH)))::set \
                   (null, "*env.m_edn_pull_agent*", "vif", edn_if); \
  end
`endif

`endif // __CIP_MACROS_SVH__
