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
  input edn_pkg::edn_rsp_t entropy_rsp_i,          // Entropy Response
  input [EntropyRateWidth-1:0] entropy_rate_i,     // Entropy Rate
  input clk_ast_es_i,                              // Entropy Clock
  input rst_ast_es_ni,                             // Entropy Reset
  input clk_src_sys_en_i,                          // System Source Clock Enable
  input clk_src_sys_jen_i,                         // System Source Clock Jitter Enable
  output edn_pkg::edn_req_t entropy_req_o          // Entropy Request
);

///////////////////////////////////////
// Entropy Enable
///////////////////////////////////////
// Entropy Logic @clk_ast_es_i clock domain
// Reset De-Assert syncronizer
logic entropy_enable, sync_rst_es_n, rst_es_n;

assign entropy_enable = (rst_ast_es_ni && clk_src_sys_en_i && clk_src_sys_jen_i);

prim_generic_flop_2sync #(
  .Width ( 1 )
) rst_es_da_sync (
  .clk_i ( clk_ast_es_i ),
  .rst_ni ( entropy_enable ),
  .d_i ( 1'b1 ),
  .q_o ( sync_rst_es_n )
);
assign rst_es_n = sync_rst_es_n;


///////////////////////////////////////
// Entropy Rate
///////////////////////////////////////
logic read_entropy, fast_start;
logic [(1<<EntropyRateWidth)-1:0] erate_cnt;
logic [32-1:0] entropy_rate;
logic [6-1:0] fast_cnt;
logic inc_fifo_cnt, dec_fifo_cnt;

always_ff @( posedge clk_ast_es_i, negedge rst_es_n ) begin
  if ( !rst_es_n )         erate_cnt <= {(1<<EntropyRateWidth){1'b0}};
  else if ( read_entropy ) erate_cnt <= {(1<<EntropyRateWidth){1'b0}};
  else                     erate_cnt <= erate_cnt + 1'b1;
end

always_ff @( posedge clk_ast_es_i, negedge rst_es_n ) begin
  if ( !rst_es_n ) begin
    fast_start <= 1'b1;
    fast_cnt   <= 6'h00;
  end
  else if ( fast_cnt == 6'h20 )
    fast_start <= 1'b0;
  else if ( fast_start && dec_fifo_cnt )
    fast_cnt   <= fast_cnt + 1'b1;
end

assign entropy_rate = fast_start ? 1 : (1 << entropy_rate_i);
assign read_entropy = (entropy_rate == 1) || (erate_cnt == entropy_rate[(1<<EntropyRateWidth)-1:0]);


///////////////////////////////////////
// Entropy FIFO
///////////////////////////////////////
//
//                            64-bit FIFO
//          32 +----------------------------------------+ 1
// edn_bus =/=>|+--------------------+ +---------------+|-/-> To LFSR
// edn_ack --->|| 32-bit prim_packer |-| 32 1-bit fifo ||---> valid (!empty)
// edn_req <---|+--------------------+ +---------------+|<--- read_entropy
//             +----------------------------------------+
//
// The FIFO level should be calculated by (32*n - bits_to_LFSR)
// A request will be issue when the 32-bit buffer is empty!
// That means, the FIFO level <= 31 (?Air? bubble cleared from the fifo)
// So, making sure the req_o is/was issued when the FIFO level < 16 will be true at all time.

// FIFO RDP/WRP/Level
logic [6-1:0] fifo_cnt;            // For 32 1-bit FIFO
logic [5-1:0] fifo_rdp, fifo_wrp;  // FIFO read pointer & write pointer
logic [32-1:0] fifo_data;          // 32 1-bit FIFO
logic fifo_full, fifo_empty;

logic entropy_req, entropy_ack, entropy_bit, entropy_bit_valid;
logic [6-1:0] entropy_depth_o;
logic [32-1:0] entropy_bus;

assign entropy_req_o.edn_req = entropy_req;
assign entropy_ack = entropy_rsp_i.edn_ack;
assign entropy_bus = entropy_rsp_i.edn_bus;

prim_packer_fifo #(
  .InW ( 32 ),
  .OutW ( 1 )
) u_pached_fifo (
  .clk_i ( clk_ast_es_i ),
  .rst_ni ( rst_es_n ),
  .clr_i ( 1'b0 ),                      // Not used
  .wvalid_i ( entropy_ack ),            // EDN_ACK
  .wdata_i (  entropy_bus ),            // EDN_BUS (32-bit)
  .wready_o ( entropy_req ),            // EDN_REQ
  //
  .rvalid_o ( entropy_bit_valid ),      // Entropy bit is valid
  .rdata_o ( entropy_bit ),             // Entropy bit
  .rready_i ( !fifo_full ),             // FIFO is not full
  .depth_o ( entropy_depth_o[6-1:0] )   // empty when (entropy_depth_o == `0)
);

assign fifo_full  = (fifo_cnt == 6'h20);
assign fifo_empty = (fifo_cnt == 6'h00);

assign inc_fifo_cnt = !fifo_full && entropy_bit_valid;
assign dec_fifo_cnt = !fifo_empty && read_entropy;

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

// FIFO Write
always_ff @( posedge clk_ast_es_i, negedge rst_es_n ) begin
  if ( !rst_es_n )         fifo_data[32-1:0]   <= {32{1'b0}};
  else if ( inc_fifo_cnt ) fifo_data[fifo_wrp] <= entropy_bit;
end

// FIFO Read Out
wire fifo_entropy_out = fifo_data[fifo_rdp];


endmodule  // of entropy
