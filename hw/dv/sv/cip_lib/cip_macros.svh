// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef __CIP_MACROS_SVH__
`define __CIP_MACROS_SVH__

// Declare array of alert interface, using parameter NUM_ALERTS and LIST_OF_ALERTS, and connect to
// arrays of wires (alert_tx and alert_rx). User need to manually connect these wires to DUT
// Also set each alert_if to uvm_config_db to use in env.
`ifndef DV_ALERT_IF_CONNECT
`define DV_ALERT_IF_CONNECT(CLK_ = clk, RST_N_ = rst_n) \
  alert_esc_if alert_if[NUM_ALERTS](.clk(CLK_), .rst_n(RST_N_)); \
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
`ifndef DV_EDN_IF_CONNECT
`define DV_EDN_IF_CONNECT \
  wire edn_rst_n; \
  wire edn_clk; \
  clk_rst_if edn_clk_rst_if(.clk(edn_clk), .rst_n(edn_rst_n)); \
  push_pull_if #(.DeviceDataWidth(cip_base_pkg::EDN_DATA_WIDTH)) edn_if[NUM_EDN]( \
  .clk(edn_clk), \
  .rst_n(edn_rst_n)); \
  initial begin \
    edn_clk_rst_if.set_active(); \
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "edn_clk_rst_vif", edn_clk_rst_if); \
  end \
  for (genvar i = 0; i < NUM_EDN; i++) begin : connect_edn_pins \
    initial begin \
    uvm_config_db#(virtual push_pull_if#(.DeviceDataWidth(cip_base_pkg::EDN_DATA_WIDTH))):: \
                           set(null, $sformatf("*env.m_edn_pull_agent[%0d]", i), "vif", edn_if[i]); \
    end \
  end
`endif

// A macro to simplify the distribution constraint of mubi type variable
// Don't use this macro directly, use DV_MUBI4|8|16_DIST.
// The weights of both TRUE and FALSE are scaled by the number of other
// values, and this uses ":=" for the distribution of other values, so they
// are truly uniform.
// The MAX_ argument is the maximum value that VAR_ can take, which means
// (MAX_ - 1) is the scaling factor.
`ifndef _DV_MUBI_DIST
`define _DV_MUBI_DIST(VAR_, TRUE_, FALSE_, MAX_, T_WEIGHT_, F_WEIGHT_, OTHER_WEIGHT_) \
  if (TRUE_ > FALSE_) { \
    VAR_ dist {TRUE_                         := (T_WEIGHT_) * ((MAX_) - 1), \
               FALSE_                        := (F_WEIGHT_) * ((MAX_) - 1), \
               [0 : FALSE_ - 1]              := (OTHER_WEIGHT_),            \
               [FALSE_ + 1 : TRUE_ - 1]      := (OTHER_WEIGHT_),            \
               [TRUE_ + 1 : (MAX_)]          := (OTHER_WEIGHT_)};           \
  } else {                                                                  \
    VAR_ dist {TRUE_                         := (T_WEIGHT_) * ((MAX_) - 1), \
               FALSE_                        := (F_WEIGHT_) * ((MAX_) - 1), \
               [0 : TRUE_ - 1]               := (OTHER_WEIGHT_),            \
               [TRUE_ + 1 : FALSE_ - 1]      := (OTHER_WEIGHT_),            \
               [FALSE_+ 1 : (MAX_)]          := (OTHER_WEIGHT_)};           \
  }
`endif

// inputs of these macros
// VAR: the mubi variable
// T_WEIGHT_: randomization weight of the value True
// F_WEIGHT_: randomization weight of the value False
// OTHER_WEIGHT_: randomization weight of values other than True or False
`ifndef DV_LC_TX_DIST
`define DV_LC_TX_DIST(VAR_, T_WEIGHT_ = 2, F_WEIGHT_ = 2, OTHER_WEIGHT_ = 1) \
  `_DV_MUBI_DIST(VAR_, lc_ctrl_pkg::On, lc_ctrl_pkg::Off, (1 << 4) - 1, T_WEIGHT_, F_WEIGHT_, \
                 OTHER_WEIGHT_)
`endif

`ifndef DV_MUBI4_DIST
`define DV_MUBI4_DIST(VAR_, T_WEIGHT_ = 2, F_WEIGHT_ = 2, OTHER_WEIGHT_ = 1) \
  `_DV_MUBI_DIST(VAR_, MuBi4True, MuBi4False, (1 << 4) - 1, T_WEIGHT_, F_WEIGHT_, OTHER_WEIGHT_)
`endif

`ifndef DV_MUBI8_DIST
`define DV_MUBI8_DIST(VAR_, T_WEIGHT_ = 2, F_WEIGHT_ = 2, OTHER_WEIGHT_ = 1) \
  `_DV_MUBI_DIST(VAR_, MuBi8True, MuBi8False, (1 << 8) - 1, T_WEIGHT_, F_WEIGHT_, OTHER_WEIGHT_)
`endif

`ifndef DV_MUBI12_DIST
`define DV_MUBI12_DIST(VAR_, T_WEIGHT_ = 2, F_WEIGHT_ = 2, OTHER_WEIGHT_ = 1) \
  `_DV_MUBI_DIST(VAR_, MuBi12True, MuBi12False, (1 << 12) - 1,T_WEIGHT_, F_WEIGHT_, OTHER_WEIGHT_)
`endif

`ifndef DV_MUBI16_DIST
`define DV_MUBI16_DIST(VAR_, T_WEIGHT_ = 2, F_WEIGHT_ = 2, OTHER_WEIGHT_ = 1) \
  `_DV_MUBI_DIST(VAR_, MuBi16True, MuBi16False, T_WEIGHT_, (1 << 16) - 1, F_WEIGHT_, OTHER_WEIGHT_)
`endif


// A macro to simplify the creation of coverpoints for lc_tx_t variables.
`ifndef DV_LC_TX_T_CP_BINS
`define DV_LC_TX_T_CP_BINS         \
    bins on = {lc_ctrl_pkg::On};   \
    bins off = {lc_ctrl_pkg::Off}; \
    bins others = default;
`endif

// A macro to simplify the creation of coverpoints for mubi4_t variables.
`ifndef DV_MUBI4_CP_BINS
`define DV_MUBI4_CP_BINS                      \
    bins true = {prim_mubi_pkg::MuBi4True};   \
    bins false = {prim_mubi_pkg::MuBi4False}; \
    bins others = default;
`endif

`endif  // __CIP_MACROS_SVH__
