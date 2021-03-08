// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: ast_entropy
// *Module Description:  AST Entropy
//############################################################################

module ast_entropy #(
  parameter int EntropyRateWidth = 4
) (
  input edn_pkg::edn_rsp_t entropy_rsp_i,          // Entropy Response
  input [EntropyRateWidth-1:0] entropy_rate_i,     // Entropy Rate
  input clk_ast_es_i,                              // Entropy Clock
  input rst_ast_es_ni,                             // Entropy Reset
  input clk_src_sys_en_i,                          // System Source Clock Enable
  input clk_src_sys_jen_i,                         // System Source Clock Jitter Enable
  input scan_mode_i,                               // Scan Mode
  input scan_reset_ni,                             // Scane Reset
  output edn_pkg::edn_req_t entropy_req_o          // Entropy Request
);

///////////////////////////////////////
// Entropy Reset
///////////////////////////////////////
// Entropy Logic @clk_ast_es_i clock domain
// Reset De-Assert syncronizer
logic entropy_reset_n, sync_rst_es_n, rst_es_n;

// To eable Syncronizer FFs reset in Scan Mode
assign entropy_reset_n = scan_mode_i ? scan_reset_ni :
          (rst_ast_es_ni && clk_src_sys_en_i && clk_src_sys_jen_i);
prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_rst_es_da_sync (
  .clk_i ( clk_ast_es_i ),
  .rst_ni ( entropy_reset_n ),
  .d_i ( 1'b1 ),
  .q_o ( sync_rst_es_n )
);
assign rst_es_n = scan_mode_i ? scan_reset_ni : sync_rst_es_n;


///////////////////////////////////////
// Entropy Rate
///////////////////////////////////////
logic read_entropy, fast_start;
logic [(1<<EntropyRateWidth)-1:0] erate_cnt;
logic [32-1:0] entropy_rate;
logic [6-1:0] fast_cnt;
logic inc_fifo_cnt, dec_fifo_cnt;
logic [EntropyRateWidth-1:0] sync_entropy_rate;

prim_flop_2sync #(
  .Width ( EntropyRateWidth ),
  .ResetValue ( {EntropyRateWidth{1'b0}} )
) erate_sync (
  .clk_i ( clk_ast_es_i ),
  .rst_ni ( rst_es_n ),
  .d_i ( entropy_rate_i ),
  .q_o ( sync_entropy_rate )
);

// Fastest rate to init the LFSR
always_ff @( posedge clk_ast_es_i, negedge rst_es_n ) begin
  if ( !rst_es_n ) begin
    fast_start <= 1'b1;
    fast_cnt   <= 6'h00;
  end else if ( fast_cnt == 6'h20 ) begin
    fast_start <= 1'b0;
  end else if ( fast_start && dec_fifo_cnt ) begin
    fast_cnt   <= fast_cnt + 1'b1;
  end
end

assign entropy_rate = fast_start ? 0 : ((1 << sync_entropy_rate) - 1);

always_ff @( posedge clk_ast_es_i, negedge rst_es_n ) begin
  if ( !rst_es_n ) begin
    erate_cnt <= '0;
  end else if ( read_entropy ) begin
    erate_cnt <= entropy_rate[(1<<EntropyRateWidth)-1:0];
  end else begin
    erate_cnt <= erate_cnt - 1'b1;
  end
end

assign read_entropy = (erate_cnt == '0);


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
// So, making sure the req_o is/was issued when the FIFO level < 16 will
// be true at all time.

logic entropy_req, entropy_ack;
logic entropy_req_wrdy, set_entropy_req, clr_entropy_req;
logic [32-1:0] entropy_bus;

assign set_entropy_req = !entropy_ack && entropy_req_wrdy;
assign clr_entropy_req =  entropy_ack;

always_ff @( posedge clk_ast_es_i, negedge rst_ast_es_ni ) begin
  if ( !rst_ast_es_ni ) begin
    entropy_req <= 1'b0;
  end else if ( set_entropy_req ) begin
    entropy_req <= 1'b1;
  end else if ( clr_entropy_req ) begin
    entropy_req <= 1'b0;
  end
end

assign entropy_req_o.edn_req = entropy_req;
assign entropy_ack = entropy_rsp_i.edn_ack;
assign entropy_bus = entropy_rsp_i.edn_bus;


// 32-bit Packer FIFO
////////////////////////////////////////
logic entropy_clr, entropy_bit, entropy_bit_valid;
logic [6-1:0] entropy_depth_o;
logic fifo_full;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_entropy_clr_sync (
  .clk_i ( clk_ast_es_i ),
  .rst_ni ( rst_ast_es_ni ),
  .d_i ( !(clk_src_sys_en_i && clk_src_sys_jen_i) ),
  .q_o ( entropy_clr )
);

prim_packer_fifo #(
  .InW ( 32 ),
  .OutW ( 1 )
) u_pached_fifo (
  .clk_i ( clk_ast_es_i ),
  .rst_ni ( rst_ast_es_ni ),
  .clr_i ( entropy_clr ),               // EDN Clear
  .wvalid_i ( entropy_ack ),            // EDN_ACK
  .wdata_i (  entropy_bus ),            // EDN_BUS (32-bit)
  .wready_o ( entropy_req_wrdy ),       // Set EDN_REQ Write Ready
  //
  .rvalid_o ( entropy_bit_valid ),      // Entropy bit is valid
  .rdata_o ( entropy_bit ),             // Entropy bit
  .rready_i ( !fifo_full ),             // FIFO is not full
  .depth_o ( entropy_depth_o[6-1:0] )   // empty when (entropy_depth_o == `0)
);


// 32 1-bit FIFO
////////////////////////////////////////
logic [6-1:0] fifo_cnt;            // For 32 1-bit FIFO
logic [5-1:0] fifo_rdp, fifo_wrp;  // FIFO read pointer & write pointer
logic [32-1:0] fifo_data;          // 32 1-bit FIFO
logic fifo_empty;

assign fifo_full  = (fifo_cnt == 6'h20);
assign fifo_empty = (fifo_cnt == 6'h00);

assign inc_fifo_cnt = !fifo_full && entropy_bit_valid;
assign dec_fifo_cnt = !fifo_empty && read_entropy;

always_ff @( posedge clk_ast_es_i, negedge rst_es_n ) begin
  if ( !rst_es_n ) begin
    fifo_cnt <= 6'h00;
    fifo_rdp <= 5'h00;
    fifo_wrp <= 5'h00;
  end else if ( inc_fifo_cnt && dec_fifo_cnt ) begin
    fifo_rdp <= fifo_rdp + 1'b1;
    fifo_wrp <= fifo_wrp + 1'b1;
  end else if ( inc_fifo_cnt ) begin
    fifo_cnt <= fifo_cnt + 1'b1;
    fifo_wrp <= fifo_wrp + 1'b1;
  end else if ( dec_fifo_cnt ) begin
    fifo_cnt <= fifo_cnt - 1'b1;
    fifo_rdp <= fifo_rdp + 1'b1;
  end
end

// FIFO Write
always_ff @( posedge clk_ast_es_i, negedge rst_es_n ) begin
  if ( !rst_es_n ) begin
    fifo_data[32-1:0]   <= {32{1'b0}};
  end else if ( inc_fifo_cnt ) begin
    fifo_data[fifo_wrp] <= entropy_bit;
  end
end

// FIFO Read Out
wire fifo_entropy_out = fifo_data[fifo_rdp];


endmodule : ast_entropy
