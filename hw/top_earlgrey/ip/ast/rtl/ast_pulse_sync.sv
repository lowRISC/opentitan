// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: ast_pulse_symc
// *Module Description: AST Pulse Synchronizer
//
// Synchronizes a pulse from source clock domain (clk_src) to destination
// clock domain (clk_dst). The source pulse can have any length of the
// source clock cycle.
// The destination pulse has the length of one destination clock cycle.
// Consecutive pulses need to be spaced appropriately apart from each other
// depending on the clock frequency ratio of the two clock domains.
//############################################################################

`include "prim_assert.sv"

module ast_pulse_sync (
  input scan_mode_i,
  // source clock domain
  input clk_src_i,
  input rst_src_ni,
  input src_pulse_i,
  output logic src_pulse_en_o,
  output logic src_busy_o,
  // destination clock domain
  input clk_dst_i,
  input rst_dst_ni,
  output logic dst_pulse_o
);

// Reset all flops by both resets
////////////////////////////////////////
logic rst_src_n, rst_dst_da_n;
logic rst_dst_n, rst_src_da_n;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_rst_dst_da (
  .clk_i ( clk_src_i),
  .rst_ni ( rst_dst_ni ),
  .d_i ( 1'b1 ),
  .q_o ( rst_dst_da_n )
);

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_rst_src_da (
  .clk_i ( clk_dst_i),
  .rst_ni ( rst_src_ni ),
  .d_i ( 1'b1 ),
  .q_o ( rst_src_da_n )
);

assign rst_src_n = scan_mode_i ? rst_src_ni : rst_src_ni && rst_dst_da_n;
assign rst_dst_n = scan_mode_i ? rst_dst_ni : rst_dst_ni && rst_src_da_n;


// Pulse Rising Edge Detect & Block
///////////////////////////////////////
logic src_pulse_d;

always_ff @( posedge clk_src_i, negedge rst_src_n ) begin
  if ( !rst_src_n ) begin
    src_pulse_d <= 1'b0;
  end else begin
    src_pulse_d <= src_pulse_i;
  end
end

assign src_pulse_en_o = src_pulse_i & !src_pulse_d & !src_busy_o;


// Pulse Transformation
///////////////////////////////////////
logic src_req;

// Convert src_pulse_en to a level signal
always_ff @( posedge clk_src_i, negedge rst_src_n ) begin
 if ( !rst_src_n ) begin
   src_req <= 1'b0;
  end else begin
   src_req <= (src_pulse_en_o ^ src_req);
  end
end


// SRC_REQ Synchronizer to DST
///////////////////////////////////////
logic dst_req;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_dst_req (
  .clk_i ( clk_dst_i ),
  .rst_ni ( rst_dst_n ),
  .d_i ( src_req ),
  .q_o ( dst_req )
);


// DST_REQ Synchronizer to SRC for ACK
///////////////////////////////////////
logic src_ack;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sync2_ack (
  .clk_i ( clk_src_i ),
  .rst_ni ( rst_src_n ),
  .d_i ( dst_req ),
  .q_o ( src_ack )
);

// Source is BUSY when REQ not equel to ACK
assign src_busy_o = (src_req ^ src_ack);


// Pulse Reconstruction
///////////////////////////////////////
logic dst_req_d;

always_ff @( posedge clk_dst_i, negedge rst_dst_n ) begin
  if ( !rst_dst_n ) begin
    dst_req_d <= 1'b0;
  end else begin
    dst_req_d <= dst_req;
  end
end

assign dst_pulse_o = (dst_req ^ dst_req_d);


////////////////////
// Assertions
////////////////////

// A new PULSE can only be introduced when source is not BUSY.
`ASSERT(NewPulseWhenSrcBusy, $rose(src_pulse_i) |-> !src_busy_o, clk_src_i, !rst_src_n)

`ASSERT(DstPulseCheck_A, dst_pulse_o |=> !dst_pulse_o, clk_dst_i, !rst_dst_n)

endmodule : ast_pulse_sync
