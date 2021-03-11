// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src top level wrapper file

`include "prim_assert.sv"


module entropy_src
  import entropy_src_pkg::*;
  import entropy_src_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  parameter int EsFifoDepth = 4
) (
  input logic clk_i,
  input logic rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Efuse Interface
  input logic efuse_es_sw_reg_en_i,

  // Entropy Interface
  input  entropy_src_hw_if_req_t entropy_src_hw_if_i,
  output entropy_src_hw_if_rsp_t entropy_src_hw_if_o,

  // RNG Interface
  output entropy_src_rng_req_t entropy_src_rng_o,
  input  entropy_src_rng_rsp_t entropy_src_rng_i,

  // External Health Test Interface
  output entropy_src_xht_req_t entropy_src_xht_o,
  input  entropy_src_xht_rsp_t entropy_src_xht_i,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Interrupts
  output logic    intr_es_entropy_valid_o,
  output logic    intr_es_health_test_failed_o,
  output logic    intr_es_fatal_err_o
);

  import entropy_src_reg_pkg::*;

  entropy_src_reg2hw_t reg2hw;
  entropy_src_hw2reg_t hw2reg;

  logic [NumAlerts-1:0] alert_test;
  logic [NumAlerts-1:0] alert;

  entropy_src_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o(),
    .devmode_i(1'b1)
  );

  entropy_src_core #(
    .EsFifoDepth(EsFifoDepth)
  ) u_entropy_src_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    .efuse_es_sw_reg_en_i,

    .entropy_src_hw_if_o,
    .entropy_src_hw_if_i,

    .entropy_src_xht_o,
    .entropy_src_xht_i,

    .entropy_src_rng_o,
    .entropy_src_rng_i,

    .recov_alert_o(alert[0]),
    .fatal_alert_o(alert[1]),

    .recov_alert_test_o(alert_test[0]),
    .fatal_alert_test_o(alert_test[1]),

    .intr_es_entropy_valid_o,
    .intr_es_health_test_failed_o,
    .intr_es_fatal_err_o
  );


  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(i)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alert[i]      ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  // Outputs should have a known value after reset
  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)

  // Entropy Interface
  `ASSERT_KNOWN(EsHwIfEsAckKnownO_A, entropy_src_hw_if_o.es_ack)
  `ASSERT_KNOWN(EsHwIfEsBitsKnownO_A, entropy_src_hw_if_o.es_bits)
  `ASSERT_KNOWN(EsHwIfEsFipsKnownO_A, entropy_src_hw_if_o.es_fips)

  // RNG Interface
  `ASSERT_KNOWN(EsRngEnableKnownO_A, entropy_src_rng_o.rng_enable)

  // External Health Test Interface
  `ASSERT_KNOWN(EsXhtEntropyBitKnownO_A, entropy_src_xht_o.entropy_bit)
  `ASSERT_KNOWN(EsXhtEntropyBitValidKnownO_A, entropy_src_xht_o.entropy_bit_valid)
  `ASSERT_KNOWN(EsXhtClearKnownO_A, entropy_src_xht_o.clear)
  `ASSERT_KNOWN(EsXhtActiveKnownO_A, entropy_src_xht_o.active)
  `ASSERT_KNOWN(EsXhtThreshHiKnownO_A, entropy_src_xht_o.thresh_hi)
  `ASSERT_KNOWN(EsXhtThreshLoKnownO_A, entropy_src_xht_o.thresh_lo)
  `ASSERT_KNOWN(EsXhtWindowKnownO_A, entropy_src_xht_o.window)

  // Alerts
  `ASSERT_KNOWN(AlertTxKnownO_A, alert_tx_o)

  // Interrupts
  `ASSERT_KNOWN(IntrEsEntropyValidKnownO_A, intr_es_entropy_valid_o)
  `ASSERT_KNOWN(IntrEsHealthTestFailedKnownO_A, intr_es_health_test_failed_o)
  `ASSERT_KNOWN(IntrEsFifoErrKnownO_A, intr_es_fatal_err_o)

endmodule
