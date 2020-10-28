// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: gen_alert
// *Module Description:  Generic Alert
//############################################################################
`timescale 1ns / 10ps

module gen_alert (
  input clk_i,
  input rst_ni,
  input gen_alert_trig_i,
  input gen_alert_ack_i,
  output logic gen_alert_po,
  output logic gen_alert_no
);
// Behavioral Model

// Hook for testing
logic gen_alert;
assign gen_alert = 1'b0;

logic gen_alert_set, gen_alert_clr;

assign gen_alert_set = gen_alert | gen_alert_trig_i;
assign gen_alert_clr = ~gen_alert_set & gen_alert_ack_i;

always_ff @( posedge clk_i, negedge rst_ni ) begin
  if ( !rst_ni )            gen_alert_po <= 1'b0;
  else if ( gen_alert_set ) gen_alert_po <= 1'b1;
  else if ( gen_alert_clr ) gen_alert_po <= 1'b0;
end

assign gen_alert_no = ~gen_alert_po;


endmodule  // of gen_alert
