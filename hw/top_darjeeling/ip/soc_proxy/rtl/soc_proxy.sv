// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// SoC Proxy

`include "prim_assert.sv"

module soc_proxy
  import soc_proxy_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input  logic clk_i,
  input  logic rst_ni,

  input  tlul_pkg::tl_h2d_t core_tl_i,
  output tlul_pkg::tl_d2h_t core_tl_o,

  input  tlul_pkg::tl_h2d_t ctn_tl_i,
  output tlul_pkg::tl_d2h_t ctn_tl_o,

  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  output logic [3:0] intr_external_o,

  output logic wkup_internal_req_o,
  output logic wkup_external_req_o,

  output dma_pkg::lsio_trigger_t dma_lsio_trigger_o,

  output tlul_pkg::tl_h2d_t ctn_tl_h2d_o,
  input  tlul_pkg::tl_d2h_t ctn_tl_d2h_i,

  input  prim_alert_pkg::alert_tx_t [3:0]  soc_alert_req_i,
  output prim_alert_pkg::alert_ack_t [3:0] soc_alert_ack_o,

  input  logic soc_wkup_async_i,

  input  logic [3:0] soc_intr_async_i
);

  // Feed CTN TL-UL ports through.
  assign ctn_tl_h2d_o = ctn_tl_i;
  assign ctn_tl_o = ctn_tl_d2h_i;

  // Tie off unimplemented outputs temporarily.
  assign dma_lsio_trigger_o = '0;
  assign intr_external_o = '0;
  assign wkup_internal_req_o = 1'b0;
  assign wkup_external_req_o = 1'b0;
  for (genvar i = 0; i < 4; i++) begin : gen_tieoff_soc_alert_ack
    assign soc_alert_ack_o[i] = prim_alert_pkg::ALERT_ACK_DEFAULT;
  end

  // Register node
  soc_proxy_core_reg2hw_t reg2hw;
  // soc_proxy_core_hw2reg_t hw2reg;
  logic intg_err;
  soc_proxy_core_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i       (core_tl_i),
    .tl_o       (core_tl_o),
    .reg2hw,
    .intg_err_o (intg_err)
  );

  // Alert test
  logic [NumAlerts-1:0] alert_test;
  assign alert_test[0] = reg2hw.alert_test.qe & reg2hw.alert_test.q;

  // Alert sender
  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn[0]),
    .IsFatal(1)
  ) u_prim_fatal_alert_sender (
    .clk_i,
    .rst_ni,
    .alert_test_i(alert_test[0]),
    .alert_req_i(intg_err),
    .alert_ack_o(),
    .alert_state_o(),
    .alert_rx_i(alert_rx_i[0]),
    .alert_tx_o(alert_tx_o[0])
  );

  // Assertions
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])

endmodule
