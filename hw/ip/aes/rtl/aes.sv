// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES top-level wrapper

`include "prim_assert.sv"

module aes
import aes_pkg::*;
#(
    parameter bit AES192Enable = 1,  // Can be 0 (disable), or 1 (enable).
    parameter bit Masking = 0,  // Can be 0 (no masking), or
    // 1 (first-order masking) of the cipher
    // core. Masking requires the use of a
    // masked S-Box, see SBoxImpl parameter.
    // Note: currently, constant masks are
    // used, this is of course not secure.
    parameter sbox_impl_e SBoxImpl = SBoxImplLut,  // See aes_pkg.sv
    parameter int unsigned NumDelayCyclesStartTrigger = 0  // Manual start trigger delay, useful for
// SCA measurements. A value of e.g. 40
// allows the processor to go into sleep
// before AES starts operation.
) (
    input clk_i,
    input rst_ni,

    // Entropy source interface
    // TODO: This still needs to be connected.
    // See https://github.com/lowRISC/opentitan/issues/1005
    //output logic              entropy_req_o,
    //input  logic              entropy_ack_i,
    //input  logic [63:0]       entropy_i,

    // Idle indicator for clock manager
    output logic idle_o,

    // Bus interface
    input  tlul_pkg::tl_h2d_t tl_i,
    output tlul_pkg::tl_d2h_t tl_o,

    // Alerts
    input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
    output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o
);

  import aes_reg_pkg::*;

  aes_reg2hw_t reg2hw;
  aes_hw2reg_t hw2reg;

  logic prng_data_req;
  logic prng_data_ack;
  logic [63:0] prng_data;
  logic prng_reseed_req;
  logic prng_reseed_ack;

  logic [NumAlerts-1:0] alert;

  aes_reg_top u_reg (
      .clk_i,
      .rst_ni,
      .tl_i,
      .tl_o,
      .reg2hw,
      .hw2reg,
      .devmode_i(1'b1)
  );

  aes_core #(
      .AES192Enable(AES192Enable),
      .Masking(Masking),
      .SBoxImpl(SBoxImpl),
      .NumDelayCyclesStartTrigger(NumDelayCyclesStartTrigger)
  ) u_aes_core (
      .clk_i,
      .rst_ni,

      .prng_data_req_o  (prng_data_req),
      .prng_data_ack_i  (prng_data_ack),
      .prng_data_i      (prng_data),
      .prng_reseed_req_o(prng_reseed_req),
      .prng_reseed_ack_i(prng_reseed_ack),

      .ctrl_err_o(alert[0]),

      .reg2hw,
      .hw2reg
  );

  aes_prng u_aes_prng (
      .clk_i,
      .rst_ni,

      .data_req_i  (prng_data_req),
      .data_ack_o  (prng_data_ack),
      .data_o      (prng_data),
      .reseed_req_i(prng_reseed_req),
      .reseed_ack_o(prng_reseed_ack),

      // TODO: This still needs to be connected to the entropy source.
      // See https://github.com/lowRISC/opentitan/issues/1005
      .entropy_req_o(),
      .entropy_ack_i(1'b1),
      .entropy_i    (64'hFEDCBA9876543210)
  );

  assign idle_o = hw2reg.status.idle.d;

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
        .AsyncOn(AlertAsyncOn[i])
    ) u_alert_sender_i (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .alert_i   (alert[i]),
        .alert_rx_i(alert_rx_i[i]),
        .alert_tx_o(alert_tx_o[i])
    );
  end

  // All outputs should have a known value after reset
  `ASSERT_KNOWN(TlODValidKnown, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAReadyKnown, tl_o.a_ready)
  `ASSERT_KNOWN(IdleKnown, idle_o)
  `ASSERT_KNOWN(AlertTxKnown, alert_tx_o)

endmodule
