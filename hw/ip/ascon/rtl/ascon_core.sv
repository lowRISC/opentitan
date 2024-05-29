// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon core implementation

module ascon_core
  import ascon_reg_pkg::*;
  import ascon_pkg::*;
(
  input clk_i,
  input rst_ni,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  // Alerts
  output logic alert_recov_o,
  output logic alert_fatal_o,

  // Key Manager
  input keymgr_pkg::hw_key_req_t keymgr_key_i,

  // Bus Interface
  input  ascon_reg2hw_t reg2hw,
  output ascon_hw2reg_t hw2reg
);

assign alert_recov_o = 1'b0;
assign alert_fatal_o = 1'b0;

lc_ctrl_pkg::lc_tx_t unused_lc_escalate_en_i;
assign unused_lc_escalate_en_i = lc_escalate_en_i;

keymgr_pkg::hw_key_req_t unused_keymgr_key_i;
assign unused_keymgr_key_i = keymgr_key_i;

ascon_reg2hw_t unused_reg2hw;
assign unused_reg2hw = reg2hw;

assign hw2reg = 'b0;

// TODO
logic d, q;
assign d = keymgr_key_i.valid;

logic unused_q;
assign unused_q = q;

always_ff @(posedge clk_i or negedge rst_ni) begin : test_reg
  if (!rst_ni) begin
    q <= 1'b0;
  end else begin
    q <= d;
  end
end



endmodule
