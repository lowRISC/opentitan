// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng top level wrapper file

`include "prim_assert.sv"

module csrng
 import csrng_pkg::*;
 import csrng_reg_pkg::*;
#(
  parameter aes_pkg::sbox_impl_e SBoxImpl = aes_pkg::SBoxImplCanright,
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  parameter int NHwApps = 2
) (
  input logic         clk_i,
  input logic         rst_ni,

  // Tilelink Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Efuse Interface
  input logic efuse_sw_app_enable_i,

  // Lifecycle broadcast inputs
  input  lc_ctrl_pkg::lc_tx_t  lc_hw_debug_en_i,

  // Entropy Interface
  output entropy_src_pkg::entropy_src_hw_if_req_t entropy_src_hw_if_o,
  input  entropy_src_pkg::entropy_src_hw_if_rsp_t entropy_src_hw_if_i,

  // Application Interfaces
  input  csrng_req_t  [NHwApps-1:0] csrng_cmd_i,
  output csrng_rsp_t  [NHwApps-1:0] csrng_cmd_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Interrupts
  output logic    intr_cs_cmd_req_done_o,
  output logic    intr_cs_entropy_req_o,
  output logic    intr_cs_hw_inst_exc_o,
  output logic    intr_cs_fatal_err_o
);


  import csrng_reg_pkg::*;

  csrng_reg2hw_t reg2hw;
  csrng_hw2reg_t hw2reg;

  logic  alert;
  logic  alert_test;

  csrng_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o(),
    .devmode_i(1'b1)
  );

  csrng_core #(
    .SBoxImpl(SBoxImpl),
    .NHwApps(NHwApps)
  ) u_csrng_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    // misc inputs
    .efuse_sw_app_enable_i,
    .lc_hw_debug_en_i,

    // Entropy Interface
    .entropy_src_hw_if_o,
    .entropy_src_hw_if_i,

    // Application Interfaces
    .csrng_cmd_i,
    .csrng_cmd_o,

    // Alerts
    .alert_test_o(alert_test),
    .fatal_alert_o(alert),

    .intr_cs_cmd_req_done_o,
    .intr_cs_entropy_req_o,
    .intr_cs_hw_inst_exc_o,
    .intr_cs_fatal_err_o
  );


  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn[0]),
    .IsFatal(1)
  ) u_prim_alert_sender (
    .clk_i,
    .rst_ni,
    .alert_test_i  ( alert_test    ),
    .alert_req_i   ( alert         ),
    .alert_ack_o   (               ),
    .alert_state_o (               ),
    .alert_rx_i    ( alert_rx_i[0] ),
    .alert_tx_o    ( alert_tx_o[0] )
  );


  // Assertions

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  `ASSERT_KNOWN(EsReqKnownO_A, entropy_src_hw_if_o.es_req)

  // Application Interface Asserts
  for (genvar i = 0; i < NHwApps; i = i+1) begin : gen_app_if_asserts
    `ASSERT_KNOWN(CsrngReqReadyKnownO_A, csrng_cmd_o[i].csrng_req_ready)
    `ASSERT_KNOWN(CsrngRspAckKnownO_A, csrng_cmd_o[i].csrng_rsp_ack)
    `ASSERT_KNOWN(CsrngRspStsKnownO_A, csrng_cmd_o[i].csrng_rsp_sts)
    `ASSERT_KNOWN(CsrngGenbitsValidKnownO_A, csrng_cmd_o[i].genbits_valid)
    `ASSERT_KNOWN(CsrngGenbitsFipsKnownO_A, csrng_cmd_o[i].genbits_fips)
    `ASSERT_KNOWN(CsrngGenbitsBusKnownO_A, csrng_cmd_o[i].genbits_bus)
  end : gen_app_if_asserts

  // Alerts
  `ASSERT_KNOWN(AlertTxKnownO_A, alert_tx_o)

  `ASSERT_KNOWN(IntrCsCmdReqDoneKnownO_A, intr_cs_cmd_req_done_o)
  `ASSERT_KNOWN(IntrCsEntropyReqKnownO_A, intr_cs_entropy_req_o)
  `ASSERT_KNOWN(IntrCsHwInstExcKnownO_A, intr_cs_hw_inst_exc_o)
  `ASSERT_KNOWN(IntrCsFatalErrKnownO_A, intr_cs_fatal_err_o)



endmodule
