// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: edn top level wrapper file

`include "prim_assert.sv"

module edn
  import edn_pkg::*;
  import edn_reg_pkg::*;
#(
  parameter int NumEndPoints = 7,
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  parameter int BootInsCmd = 32'h0000_0001,
  parameter int BootGenCmd = 32'h00ff_f003
) (
  input logic clk_i,
  input logic rst_ni,

  // Tilelink Bus registers
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // EDN interfaces
  input  edn_req_t [NumEndPoints-1:0] edn_i,
  output edn_rsp_t [NumEndPoints-1:0] edn_o,

  // CSRNG Application Interface
  output  csrng_pkg::csrng_req_t  csrng_cmd_o,
  input   csrng_pkg::csrng_rsp_t  csrng_cmd_i,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Interrupts
  output logic      intr_edn_cmd_req_done_o,
  // TODO: add intrp
  // output logic      intr_edn_ebus_check_failed_o,
  output logic      intr_edn_fatal_err_o
);

  import edn_reg_pkg::*;

  edn_reg2hw_t reg2hw;
  edn_hw2reg_t hw2reg;

  logic [NumAlerts-1:0] alert_test;
  logic [NumAlerts-1:0] alert;

  logic [NumAlerts-1:0] intg_err_alert;
  assign intg_err_alert[0] = 1'b0;


  edn_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o(intg_err_alert[1]), // Assign this alert to the fatal alert index.
    .devmode_i(1'b1)
  );

  edn_core #(
    .NumEndPoints(NumEndPoints),
    .BootInsCmd(BootInsCmd),
    .BootGenCmd(BootGenCmd)
  ) u_edn_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    .edn_i,
    .edn_o,

    .csrng_cmd_o,
    .csrng_cmd_i,

    // Alerts

    .recov_alert_o(alert[0]),
    .fatal_alert_o(alert[1]),

    .recov_alert_test_o(alert_test[0]),
    .fatal_alert_test_o(alert_test[1]),

    .intr_edn_cmd_req_done_o,
  // TODO: add intrp - remove () below
  //  .intr_edn_ebus_check_failed_o,
    .intr_edn_ebus_check_failed_o(),
    .intr_edn_fatal_err_o
  );



  ///////////////////////////
  // Alert generation
  ///////////////////////////
  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(i)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i]                 ),
      .alert_req_i   ( alert[i] || intg_err_alert[i] ),
      .alert_ack_o   (                               ),
      .alert_state_o (                               ),
      .alert_rx_i    ( alert_rx_i[i]                 ),
      .alert_tx_o    ( alert_tx_o[i]                 )
    );
  end


  // Assertions

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)

  // Endpoint Asserts
  for (genvar i = 0; i < NumEndPoints; i = i+1) begin : gen_edn_if_asserts
    `ASSERT_KNOWN(EdnEndPointOut_A, edn_o[i])
  end : gen_edn_if_asserts

  // CSRNG Asserts
  `ASSERT_KNOWN(CsrngAppIfOut_A, csrng_cmd_o)

  // Alerts
  `ASSERT_KNOWN(AlertTxKnownO_A, alert_tx_o)

  // Interrupt Asserts
  `ASSERT_KNOWN(IntrEdnCmdReqDoneKnownO_A, intr_edn_cmd_req_done_o)
  // TODO: add intrp
  // `ASSERT_KNOWN(IntrEdnEBusCheckFailedKnownO_A, intr_edn_ebus_check_failed_o)
  `ASSERT_KNOWN(IntrEdnFifoErrKnownO_A, intr_edn_fatal_err_o)

endmodule
