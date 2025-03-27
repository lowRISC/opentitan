// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// prim_alert_to_diff: This module receives an alert signal (using the alert protocol) and
// translates it into a differentially encoded signal (without the alert protocol).
// It also handles integrity errors from the alert receiver, treating them as alerts.
//
// IMPORTANT: This primitive is NOT intended to be used in OpenTitan top-level designs.
// In top-level designs, prim_alert_{sender,receiver} pairs should be used instead.
// The intended use case of this primitive is to signal an alert through a differential
// encoding (for minimal integrity protection) to modules that do not support
// OpenTitan's alert protocol.

module prim_alert_to_diff #(
  // AsyncOn: Enables additional synchronization logic within the alert receiver.
  parameter bit AsyncOn = 1'b0
) (
  input logic                       clk_i,
  input logic                       rst_ni,
  // Alert pair (interface signals for the alert protocol)
  output prim_alert_pkg::alert_rx_t alert_rx_o,
  input  prim_alert_pkg::alert_tx_t alert_tx_i,
  // Output diff pair (differentially encoded alert signal)
  output logic                      diff_po,
  output logic                      diff_no
);

  logic integ_error;
  logic alert;

  // u_prim_alert_receiver: Instantiates the alert receiver module.
  prim_alert_receiver #(
    .AsyncOn(AsyncOn)
  ) u_prim_alert_receiver (
    .clk_i,
    .rst_ni,
    .init_trig_i  (prim_mubi_pkg::MuBi4False),
    .ping_req_i   (1'b0),
    .ping_ok_o    (),
    .integ_fail_o (integ_error),
    .alert_o      (alert),
    .alert_rx_o,
    .alert_tx_i
  );

  // Combines the decoded alert and the integrity error signal.
  // An alert is triggered if either a valid alert is received or an integrity error occurs.
  logic combined_alert;
  assign combined_alert = integ_error | alert;

  // Instantiates the differential encoder module.
  prim_diff_encode u_prim_diff_encode (
    .clk_i,
    .rst_ni,
    .req_i(combined_alert), // Input request signal (combined alert).
    .diff_po,
    .diff_no
  );
endmodule
