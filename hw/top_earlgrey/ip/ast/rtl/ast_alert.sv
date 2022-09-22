// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// -------- W A R N I N G: A U T O - G E N E R A T E D  C O D E !! -------- //
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED.
//
//############################################################################
// *Name: ast_alert
// *Module Description:  AST Alert
//############################################################################

module ast_alert (
  input clk_i,
  input rst_ni,
  input ast_pkg::ast_dif_t alert_src_i,
  input ast_pkg::ast_dif_t alert_ack_i,
  input ast_pkg::ast_dif_t alert_trig_i,
  output ast_pkg::ast_dif_t alert_req_o
);

// Unpack inputs
logic p_alert_src, n_alert_src;
assign p_alert_src = alert_src_i.p;
assign n_alert_src = alert_src_i.n;

logic p_alert_ack, n_alert_ack;
assign p_alert_ack = alert_ack_i.p;
assign n_alert_ack = alert_ack_i.n;

logic p_alert_trig, n_alert_trig;
assign p_alert_trig = alert_trig_i.p;
assign n_alert_trig = alert_trig_i.n;

// Pack outputs
logic p_alert_req, n_alert_req;

assign alert_req_o.p = p_alert_req;
assign alert_req_o.n = n_alert_req;

// P Alert
logic p_alert, set_p_alert, clr_p_alert;

assign set_p_alert =  p_alert_src || p_alert_trig;
assign clr_p_alert = !set_p_alert && p_alert_ack;

always_ff @( posedge clk_i, negedge rst_ni ) begin
  if ( !rst_ni ) begin
    p_alert <= 1'b0;
  end else if ( set_p_alert ) begin
    p_alert <= 1'b1;
  end else if ( clr_p_alert ) begin
    p_alert <= 1'b0;
  end
end

assign p_alert_req = p_alert;

// N Alert
logic n_alert, set_n_alert, clr_n_alert;

assign set_n_alert = !(n_alert_src && n_alert_trig);
assign clr_n_alert = !(set_n_alert || n_alert_ack);

always_ff @( posedge clk_i, negedge rst_ni ) begin
  if ( !rst_ni ) begin
    n_alert <= 1'b1;
  end else if ( set_n_alert ) begin
    n_alert <= 1'b0;
  end else if ( clr_n_alert ) begin
    n_alert <= 1'b1;
  end
end

assign n_alert_req = n_alert;

endmodule : ast_alert
