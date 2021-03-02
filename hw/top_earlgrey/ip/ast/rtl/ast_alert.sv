// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: ast_alert
// *Module Description:  AST Alert
//############################################################################

module ast_alert (
  input clk_i,
  input rst_ni,
  input ast_pkg::ast_dif_t alert_in_i,
  input ast_pkg::ast_dif_t alert_trig_i,
  input ast_pkg::ast_dif_t alert_ack_i,
  output ast_pkg::ast_dif_t alert_req_o
);

// Unpack inputs
logic alert_in_p, alert_in_n, alert_trig_p, alert_trig_n, alert_ack_p, alert_ack_n;

assign alert_in_p   = alert_in_i.p;
assign alert_in_n   = alert_in_i.n;
assign alert_trig_p = alert_trig_i.p;
assign alert_trig_n = alert_trig_i.n;
assign alert_ack_p  = alert_ack_i.p;
assign alert_ack_n  = alert_ack_i.n;

// Pack outputs
logic alert_req_p, alert_req_n;

assign alert_req_o.p = alert_req_p;
assign alert_req_o.n = alert_req_n;

logic alert_p, set_alert_p, clr_alert_p;

assign set_alert_p = alert_in_p || alert_trig_p;
assign clr_alert_p = !set_alert_p && alert_ack_p;

always_ff @( posedge clk_i, negedge rst_ni ) begin
  if ( !rst_ni ) begin
    alert_p <= 1'b0;
  end else if ( set_alert_p ) begin
    alert_p <= 1'b1;
  end else if ( clr_alert_p ) begin
    alert_p <= 1'b0;
  end
end

assign alert_req_p = alert_p;

logic alert_n, set_alert_n, clr_alert_n;
assign set_alert_n = !(alert_in_n && alert_trig_n);
assign clr_alert_n = !(set_alert_n || alert_ack_n);

always_ff @( posedge clk_i, negedge rst_ni ) begin
  if ( !rst_ni ) begin
    alert_n <= 1'b1;
  end else if ( set_alert_n ) begin
    alert_n <= 1'b0;
  end else if ( clr_alert_n ) begin
    alert_n <= 1'b1;
  end
end

assign alert_req_n = alert_n;

endmodule : ast_alert
