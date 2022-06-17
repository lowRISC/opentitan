// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module pattgen
  import pattgen_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input clk_i,
  input rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  output logic cio_pda0_tx_o,
  output logic cio_pcl0_tx_o,
  output logic cio_pda1_tx_o,
  output logic cio_pcl1_tx_o,
  output logic cio_pda0_tx_en_o,
  output logic cio_pcl0_tx_en_o,
  output logic cio_pda1_tx_en_o,
  output logic cio_pcl1_tx_en_o,

  output logic intr_done_ch0_o,
  output logic intr_done_ch1_o
);

  logic [NumAlerts-1:0] alert_test, alerts;
  pattgen_reg2hw_t reg2hw;
  pattgen_hw2reg_t hw2reg;

  pattgen_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o(alerts[0]),
    .devmode_i(1'b1)
  );

  assign alert_test = {
    reg2hw.alert_test.q &
    reg2hw.alert_test.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[0]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  assign cio_pda0_tx_en_o = 1'b1;
  assign cio_pcl0_tx_en_o = 1'b1;
  assign cio_pda1_tx_en_o = 1'b1;
  assign cio_pcl1_tx_en_o = 1'b1;

  pattgen_core u_pattgen_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    .pda0_tx_o(cio_pda0_tx_o),
    .pcl0_tx_o(cio_pcl0_tx_o),
    .pda1_tx_o(cio_pda1_tx_o),
    .pcl1_tx_o(cio_pcl1_tx_o),

    .intr_done_ch0_o,
    .intr_done_ch1_o
  );

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)
  `ASSERT_KNOWN(Pcl0TxKnownO_A, cio_pcl0_tx_o)
  `ASSERT_KNOWN(Pda0TxKnownO_A, cio_pda0_tx_o)
  `ASSERT_KNOWN(Pcl1TxKnownO_A, cio_pcl1_tx_o)
  `ASSERT_KNOWN(Pda1TxKnownO_A, cio_pda1_tx_o)
  `ASSERT_KNOWN(IntrCh0DoneKnownO_A, intr_done_ch0_o)
  `ASSERT_KNOWN(IntrCh1DoneKnownO_A, intr_done_ch1_o)

  `ASSERT(Pcl0TxEnIsOne_A, cio_pcl0_tx_en_o === 1'b1)
  `ASSERT(Pda0TxEnIsOne_A, cio_pda0_tx_en_o === 1'b1)
  `ASSERT(Pcl1TxEnIsOne_A, cio_pcl1_tx_en_o === 1'b1)
  `ASSERT(Pda1TxEnIsOne_A, cio_pda1_tx_en_o === 1'b1)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule : pattgen
