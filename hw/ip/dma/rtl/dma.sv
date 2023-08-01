// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module dma
  import tlul_pkg::*;
  import dma_pkg::*;
  import dma_reg_pkg::*;
#(
    parameter logic [NumAlerts-1:0] AlertAsyncOn         = {NumAlerts{1'b1}},
    parameter bit                   EnableDataIntgGen    = 1'b1,
    parameter logic [RsvdWidth-1:0] TlUserRsvd           = '0,
    parameter int                   NumLsioTriggers      = dma_pkg::NUM_LSIO_TRIGGERS,
    parameter int unsigned PlicLsioPlic[NumLsioTriggers] = '{
      32'h1234567,
      32'h1234567,
      32'h1234567,
      32'h1234567
    },
    parameter logic [SYS_RACL_WIDTH-1:0] SysRacl         = '0,
    parameter integer                  OtAgentId         = 0
) (
  input logic                                      clk_i,
  input logic                                      rst_ni,
  input logic                                      test_en_i,
  // DMA interrupt and incoming LSIO triggers
  output  logic                                    intr_dma_o,
  input   logic [(NumLsioTriggers-1):0]            lsio_trigger_i,
  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,
  // Device port
  input   tlul_pkg::tl_h2d_t                        tl_dev_i,
  output  tlul_pkg::tl_d2h_t                        tl_dev_o,
  // Facing Xbar
  input   tlul_pkg::tl_d2h_t                        tl_xbar_i,
  output  tlul_pkg::tl_h2d_t                        tl_xbar_o,
  // Host port
  input   tlul_pkg::tl_d2h_t                        tl_host_i,
  output  tlul_pkg::tl_h2d_t                        tl_host_o,
  // System port
  input  dma_pkg::sys_rsp_t                         sys_i,
  output dma_pkg::sys_req_t                         sys_o
);
  dma_reg2hw_t reg2hw;
  dma_hw2reg_t hw2reg;

  logic reg_intg_error;
  dma_reg_top u_dma_reg (
    .clk_i     ( clk_i          ),
    .rst_ni    ( rst_ni         ),
    .tl_i      ( tl_dev_i       ),
    .tl_o      ( tl_dev_o       ),
    .reg2hw    ( reg2hw         ),
    .hw2reg    ( hw2reg         ),
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o( reg_intg_error )
  );

  // Alerts
  logic [NumAlerts-1:0] alert_test, alerts;
  assign alert_test = {reg2hw.alert_test.q & reg2hw.alert_test.qe};
  assign alerts[0]  = reg_intg_error;

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i (alert_test[i]),
      .alert_req_i  (alerts[0]),
      .alert_ack_o  (),
      .alert_state_o(),
      .alert_rx_i   (alert_rx_i[i]),
      .alert_tx_o   (alert_tx_o[i])
    );
  end

  // All outputs should be known value after reset
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_dma_reg, alert_tx_o[0])
endmodule
