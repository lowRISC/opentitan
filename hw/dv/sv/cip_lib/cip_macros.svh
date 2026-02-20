// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef __CIP_MACROS_SVH__
`define __CIP_MACROS_SVH__

// Declare array of alert interface, using parameter NUM_ALERTS and LIST_OF_ALERTS, and connect to
// arrays of wires (alert_tx and alert_rx). User need to manually connect these wires to DUT.
// Also set each alert_if to uvm_config_db to use in env.
// When NUM_ALERTS is zero still instantiate one interface to avoid zero size
// array warnings.
`ifndef DV_ALERT_IF_CONNECT
`define DV_ALERT_IF_CONNECT(CLK_ = clk, RST_N_ = rst_n) \
  localparam uint dv_alert_if_connect_param = (NUM_ALERTS == 0) ? 1 : NUM_ALERTS; \
  alert_esc_if alert_if[dv_alert_if_connect_param](.clk(CLK_), .rst_n(RST_N_)); \
  prim_alert_pkg::alert_rx_t [dv_alert_if_connect_param-1:0] alert_rx; \
  prim_alert_pkg::alert_tx_t [dv_alert_if_connect_param-1:0] alert_tx; \
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

// Macros that expand to a ternary expression giving the smaller / larger of the two values.
//
// These make no guarantee to only evaluate arguments once.
`ifndef _DV_TERNARY_MIN
`define _DV_TERNARY_MIN(a_, b_) (((a_) < (b_)) ? (a_) : (b_))
`endif
`ifndef _DV_TERNARY_MAX
`define _DV_TERNARY_MAX(a_, b_) (((a_) < (b_)) ? (b_) : (a_))
`endif

// A macro that expands to a constraint giving distribution for a mubi-type variable
// Don't use this macro directly: use DV_MUBI4|8|16_DIST instead.
//
// Arguments:
//
//  VAR_           The variable whose distribution is being constrained
//  TRUE_          MuBi true value
//  FALSE_         MuBi false value
//  MAX_           The maximum value in the bit-vector range for the value
//  T_WEIGHT_      A weight to give the "true" case
//  F_WEIGHT_      A weight to give the "false" case
//  OTHER_WEIGHT_  A weight to give all other cases
//
// This macro uses ":=" to give weights for the other cases in order that the individual values
// won't have a weight that depends on the length of the range containing them. There are (MAX_ - 3)
// items in these other ranges, so we scale T_WEIGHT and F_WEIGHT by that value to ensure that
// T_WEIGHT/F_WEIGHT/OTHER_WEIGHT give the relative probabilities of true/false/something-else.
//
// Some tools generate a warning if there is a backwards range ([big:little]) in the distribution,
// even if an if/else check ensures that it isn't used. To avoid this warning, we use a ternary
// operator to extract the larger/smaller value.
`ifndef _DV_MUBI_DIST
`define _DV_MUBI_DIST(VAR_, TRUE_, FALSE_, MAX_, T_WEIGHT_, F_WEIGHT_, OTHER_WEIGHT_)  \
  VAR_ dist {                                                                          \
    TRUE_                                        := (T_WEIGHT_) * ((MAX_) - 3),        \
    FALSE_                                       := (F_WEIGHT_) * ((MAX_) - 3),        \
    [0 : `_DV_TERNARY_MIN(TRUE_, FALSE_)-1]      := (OTHER_WEIGHT_),                   \
    [(`_DV_TERNARY_MIN(TRUE_, FALSE_)+1) :                                             \
     (`_DV_TERNARY_MAX(TRUE_, FALSE_)-1)]        := (OTHER_WEIGHT_),                   \
    [(`_DV_TERNARY_MAX(TRUE_, FALSE_)+1):(MAX_)] := (OTHER_WEIGHT_)                    \
  };
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
