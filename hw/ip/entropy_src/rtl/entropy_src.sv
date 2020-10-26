// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src top level wrapper file


module entropy_src import entropy_src_pkg::*; #(
  parameter int unsigned EsFifoDepth = 2
) (
  input  clk_i,
  input  rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Efuse Interface
  input efuse_es_sw_reg_en_i,

  // Entropy Interface
  input  entropy_src_hw_if_req_t entropy_src_hw_if_i,
  output entropy_src_hw_if_rsp_t entropy_src_hw_if_o,

  // RNG Interface
  output entropy_src_rng_req_t entropy_src_rng_o,
  input  entropy_src_rng_rsp_t entropy_src_rng_i,

  // Alerts
  input  prim_alert_pkg::alert_rx_t alert_rx_i,
  output prim_alert_pkg::alert_tx_t alert_tx_o,

  // Interrupts
  output logic    es_entropy_valid_o,
  output logic    es_health_test_failed_o,
  output logic    es_fifo_err_o
);

  import entropy_src_reg_pkg::*;

  entropy_src_reg2hw_t reg2hw;
  entropy_src_hw2reg_t hw2reg;

  logic alert_event;

  entropy_src_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,

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

    .entropy_src_rng_o,
    .entropy_src_rng_i,

    .alert_event_o(alert_event),

    .es_entropy_valid_o,
    .es_health_test_failed_o,
    .es_fifo_err_o
  );

   prim_alert_sender #(
     .AsyncOn(1'b1)
   ) u_alert_sender_i (
     .clk_i      ( clk_i      ),
     .rst_ni     ( rst_ni     ),
     .alert_req_i( alert_event),
     .alert_ack_o(            ),
     .alert_rx_i ( alert_rx_i ),
     .alert_tx_o ( alert_tx_o )
   );

  // Outputs should have a known value after reset
  `ASSERT_KNOWN(AlertTxKnown, alert_tx_o)

endmodule
