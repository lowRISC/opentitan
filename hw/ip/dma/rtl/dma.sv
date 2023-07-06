// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module dma
  import tlul_pkg::*;
  import dma_pkg::*;
  import dma_reg_pkg::*;
#(
    parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
    parameter integer NumLsioTriggers            = 4,
    parameter integer SysNumRnReqCh              = 2,
    parameter integer AgtReqMetadataWidth        = 7,
    parameter integer AgtReqDataByteWidth        = 4,
    parameter integer NumSysErrorTypes           = 1,
    parameter integer RaclWidth                  = 4,
    parameter integer DmaAddrWidth               = 64
) (
  input logic                                                          clk_i,
  input logic                                                          rst_ni,
  input logic                                                          test_en_i,
  // DMA interrupt and incoming LSIO interrupts
  output  logic                                                        intr_dma_o,
  input   logic [(NumLsioTriggers-1):0]                                lsio_trigger_i,
  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0]                    alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0]                    alert_tx_o,
  // facing scs's xbar
  input   tlul_pkg::tl_d2h_t                                           tl_xbar_i,
  output  tlul_pkg::tl_h2d_t                                           tl_xbar_o,
  // Device port
  input   tlul_pkg::tl_h2d_t                                           tl_dev_i,
  output  tlul_pkg::tl_d2h_t                                           tl_dev_o,
  // Host port
  input   tlul_pkg::tl_d2h_t                                           tl_host_i,
  output  tlul_pkg::tl_h2d_t                                           tl_host_o,
  // System port
  output logic     [(SysNumRnReqCh-1):0]                            sys_req_vld_vec_o,
  output logic     [(SysNumRnReqCh-1):0][(AgtReqMetadataWidth-1):0] sys_req_metadata_vec_o,
  output sys_opc_e [(SysNumRnReqCh-1):0]                            sys_req_opcode_vec_o,
  output logic     [(SysNumRnReqCh-1):0][(DmaAddrWidth-1):0]        sys_req_iova_vec_o,
  output logic     [(SysNumRnReqCh-1):0][(RaclWidth-1):0]           sys_req_racl_vec_o,
  // Request write data
  output logic [((AgtReqDataByteWidth*8)-1):0]                         sys_req_write_data_o,
  output logic [(AgtReqDataByteWidth-1):0]                             sys_req_write_be_o,
  output logic [(AgtReqDataByteWidth-1):0]                             sys_req_read_be_o,
  input logic                                                          sys_error_vld_i,
  input logic [(NumSysErrorTypes-1):0]                                 sys_error_vec_i,
  input logic                                                          sys_read_data_vld_i,
  input logic [((AgtReqDataByteWidth*8)-1):0]                          sys_read_data_i,
  input logic [(AgtReqMetadataWidth-1):0]                              sys_read_metadata_i,
  input logic [(SysNumRnReqCh-1):0]                                    sys_req_grant_vec_i
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
    .intg_err_o( reg_intg_error ),
    .devmode_i ( 1'b1           )
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
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_dma_reg_core, alert_tx_o[0])
endmodule
