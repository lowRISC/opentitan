// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: entropy
// *Module Description:  Entropy
//############################################################################
`timescale 1ns / 10ps

module entropy #(
  parameter int EntropyRateWidth = 4
) (
  input entropy_ack_i,
  input entropy_i,
  input [EntropyRateWidth-1:0] entropy_rate_i,
  input clk_src_sys_jen_i,                         // System Source Clock Jitter Enable
  input clk_ast_es_i,
  input rst_ast_es_ni,
  input clk_src_sys_i,
  input rst_src_sys_ni,
  input scan_mode_i,
  output logic entropy_req_o
);

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Entropy Logic @clk_ast_es_i clock domain


///////////////////////////////////////
// Entropy Enable
///////////////////////////////////////
logic entropy_enable;
assign entropy_enable = rst_ast_es_ni && clk_src_sys_jen_i;

// Reset De-Assert syncronizer
//JL TODO: Concider using Prim cell
// prim_generic_flop_2sync #(
//    .Width ( 1 )
// ) rst_es_da_sync (
//    .clk_i ( clk_ast_es_i ),
//    .rst_ni ( entropy_enable ),
//    .d_i ( 1'b1 ),
//    .q_o ( rst_es_n )
// );
logic sync1_rst_es_n, sync2_rst_es_n, rst_es_n;

always_ff @( posedge clk_ast_es_i, negedge entropy_enable ) begin
  if ( !entropy_enable ) begin
    sync1_rst_es_n <= 1'b0;
    sync2_rst_es_n <= 1'b0;
  end
  else begin
    sync1_rst_es_n <= 1'b1;
    sync2_rst_es_n <= sync1_rst_es_n;
  end
end

assign rst_es_n = scan_mode_i ? rst_ast_es_ni : sync2_rst_es_n;


///////////////////////////////////////
// Entropy Rate
///////////////////////////////////////
logic read_entropy;
logic [(1<<EntropyRateWidth)-1:0] erate_cnt;
logic [32-1:0] entropy_rate;

always_ff @( posedge clk_ast_es_i, negedge rst_es_n ) begin
  if ( !rst_es_n )         erate_cnt <= {(1<<EntropyRateWidth){1'b0}};
  else if ( read_entropy ) erate_cnt <= {(1<<EntropyRateWidth){1'b0}};
  else                     erate_cnt <= erate_cnt + 1'b1;
end

assign entropy_rate = (1 << entropy_rate_i);
assign read_entropy = (erate_cnt == entropy_rate[(1<<EntropyRateWidth)-1:0]);


///////////////////////////////////////
// Entropy FIFO
///////////////////////////////////////
// FIFO RDP/WRP/Level
logic [6-1:0] fifo_cnt;            // For 32 1-bit FIFO
logic [5-1:0] fifo_rdp, fifo_wrp;  // FIFO read pointer & write pointer
logic [32-1:0] fifo_data;          // 32 1-bi FIFOt
logic inc_fifo_cnt, dec_fifo_cnt;

assign inc_fifo_cnt = (fifo_cnt < 6'h20) && entropy_ack_i;
assign dec_fifo_cnt = (fifo_cnt != 6'h00) && read_entropy;

always_ff @( posedge clk_ast_es_i, negedge rst_es_n ) begin
  if ( !rst_es_n ) begin
    fifo_cnt <= 6'h00;
    fifo_rdp <= 5'h00;
    fifo_wrp <= 5'h00;
  end
  else if ( inc_fifo_cnt && dec_fifo_cnt ) begin
    fifo_rdp <= fifo_rdp + 1'b1;
    fifo_wrp <= fifo_wrp + 1'b1;
  end
  else if ( inc_fifo_cnt ) begin
    fifo_cnt <= fifo_cnt + 1'b1;
    fifo_wrp <= fifo_wrp + 1'b1;
  end
  else if ( dec_fifo_cnt ) begin
    fifo_cnt <= fifo_cnt - 1'b1;
    fifo_rdp <= fifo_rdp + 1'b1;
  end
end

// Request
always_ff @( posedge clk_ast_es_i, negedge rst_es_n ) begin
  if ( !rst_es_n )
    entropy_req_o <= 1'b0;
  else if ( fifo_cnt < 6'h10 )
    entropy_req_o <= 1'b1;  // Half
  else if ( (fifo_cnt == 6'h1f) && inc_fifo_cnt && ~dec_fifo_cnt )
    entropy_req_o <= 1'b0;  // Full
end

// FIFO Write
always_ff @( posedge clk_ast_es_i, negedge rst_es_n ) begin
  if ( !rst_es_n )         fifo_data[32-1:0]   <= {32{1'b0}};
  else if ( inc_fifo_cnt ) fifo_data[fifo_wrp] <= entropy_i;
end

// FIFO Read Out
wire fifo_entropy_out = fifo_data[fifo_rdp];


endmodule  // of entropy
