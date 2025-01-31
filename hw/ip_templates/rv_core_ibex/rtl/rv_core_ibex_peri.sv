// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RV core ibex peripheral
//

`include "prim_assert.sv"

module rv_core_ibex_peri
  import rv_core_ibex_peri_pkg::*;
  import rv_core_ibex_peri_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input clk_i,
  input rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // alert events from rv_core_ibex
  input alert_event_t fatal_intg_event_i,
  input alert_event_t fatal_core_event_i,
  input alert_event_t recov_core_event_i,

  // region configuration to ibex
  output region_cfg_t [NumRegions-1:0] ibus_region_cfg_o,
  output region_cfg_t [NumRegions-1:0] dbus_region_cfg_o,

  // interrupts and alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o
);

  // Register module
  rv_core_ibex_peri_reg2hw_t reg2hw;
  rv_core_ibex_peri_hw2reg_t hw2reg;

  logic intg_err;
  rv_core_ibex_peri_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o (intg_err)
  );

  ///////////////////////
  // Region assignments
  ///////////////////////

  for(genvar i = 0; i < NumRegions; i++) begin : gen_ibus_region_cfgs
    assign ibus_region_cfg_o[i].en = reg2hw.ibus_addr_en[i];
    assign ibus_region_cfg_o[i].matching_region = reg2hw.ibus_addr_matching[i];
    assign ibus_region_cfg_o[i].remap_addr = reg2hw.ibus_remap_addr[i];
  end

  for(genvar i = 0; i < NumRegions; i++) begin : gen_dbus_region_cfgs
    assign dbus_region_cfg_o[i].en = reg2hw.dbus_addr_en[i];
    assign dbus_region_cfg_o[i].matching_region = reg2hw.dbus_addr_matching[i];
    assign dbus_region_cfg_o[i].remap_addr = reg2hw.dbus_remap_addr[i];
  end

  ///////////////////////
  // Error assignment
  ///////////////////////
  logic fatal_intg_err, fatal_core_err, recov_core_err;

  assign fatal_intg_err = fatal_intg_event_i != EventOff;
  assign fatal_core_err = fatal_core_event_i != EventOff;
  assign recov_core_err = recov_core_event_i != EventOff;

  assign hw2reg.err_status.reg_intg_err.d = 1'b1;
  assign hw2reg.err_status.reg_intg_err.de = intg_err;
  assign hw2reg.err_status.fatal_intg_err.d = 1'b1;
  assign hw2reg.err_status.fatal_intg_err.de = fatal_intg_err;
  assign hw2reg.err_status.fatal_core_err.d = 1'b1;
  assign hw2reg.err_status.fatal_core_err.de = fatal_core_err;
  assign hw2reg.err_status.recov_core_err.d = 1'b1;
  assign hw2reg.err_status.recov_core_err.de = recov_core_err;

  ///////////////////////
  // Alert generation
  ///////////////////////

  logic [NumAlerts-1:0] alert_test;
  assign alert_test[0] = reg2hw.alert_test.fatal_sw_err.q &
                         reg2hw.alert_test.fatal_sw_err.qe;
  assign alert_test[1] = reg2hw.alert_test.recov_sw_err.q &
                         reg2hw.alert_test.recov_sw_err.qe;
  assign alert_test[2] = reg2hw.alert_test.fatal_hw_err.q &
                         reg2hw.alert_test.fatal_hw_err.qe;
  assign alert_test[3] = reg2hw.alert_test.recov_hw_err.q &
                         reg2hw.alert_test.recov_hw_err.qe;

  localparam bit [NumAlerts-1:0] AlertFatal = '{1, 0, 1, 0};

  logic [NumAlerts-1:0] alert_events;

  assign alert_events[0] = reg2hw.sw_alert[0].q != EventOff;
  assign alert_events[1] = reg2hw.sw_alert[1].q != EventOff;
  assign alert_events[2] = intg_err | fatal_intg_err | fatal_core_err;
  assign alert_events[3] = recov_core_err;

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_senders
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[0]),
      .IsFatal(AlertFatal[i])
    ) u_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i(alert_test[i]),
      .alert_req_i(alert_events[i]),
      .alert_ack_o(),
      .alert_state_o(),
      .alert_rx_i(alert_rx_i[i]),
      .alert_tx_o(alert_tx_o[i])
    );
  end

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[2])
endmodule // rv_core_ibex_peri
