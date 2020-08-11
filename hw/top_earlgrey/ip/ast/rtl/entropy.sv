// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: entropy
// *Module Description:  Entropy
//
//############################################################################
`timescale 1ns / 1ps

module entropy #(
    parameter int EntropyInWidth = 1,
    parameter int EntropyRateWidth = 4
) (
    input                               entropy_ack_i,
    input        [  EntropyInWidth-1:0] entropy_i,
    input        [EntropyRateWidth-1:0] entropy_rate_i,
    input                               clk_src_sys_jen_i,  // System Source Clock Jitter Enable
    input                               clk_ast_es_i,
    input                               rst_ast_es_ni,
    input                               clk_src_sys_i,
    input                               rst_src_sys_ni,
    input                               scan_mode_i,
    output logic                        entropy_req_o
);


  ///////////////////////////////////
  // Entropy & Jitter
  ///////////////////////////////////

  // Entropy Enable
  logic entropy_enable;

  assign entropy_enable = rst_ast_es_ni && clk_src_sys_jen_i;

  // Reset De-Assert syncronizer
  logic sync1_rst_es_n, sync2_rst_es_n, rst_es_n;

  always_ff @(posedge clk_ast_es_i, negedge entropy_enable) begin
    if (!entropy_enable) begin
      sync1_rst_es_n <= 1'b0;
      sync2_rst_es_n <= 1'b0;
    end else begin
      sync1_rst_es_n <= 1'b1;
      sync2_rst_es_n <= sync1_rst_es_n;
    end
  end

  assign rst_es_n = scan_mode_i ? rst_ast_es_ni : sync2_rst_es_n;

  // Entropy Rate
  logic [(1<<EntropyRateWidth)-1:0] rate_cnt;
  logic [32-1:0] entropy_rate;
  logic read_entropy;

  always_ff @(posedge clk_ast_es_i, negedge rst_es_n) begin
    if (!rst_es_n) rate_cnt <= {(1 << EntropyRateWidth) {1'b0}};
    else if (read_entropy) rate_cnt <= {(1 << EntropyRateWidth) {1'b0}};
    else rate_cnt <= rate_cnt + 1'b1;
  end

  assign entropy_rate = (1 << entropy_rate_i);
  assign read_entropy = (rate_cnt == entropy_rate[(1 << EntropyRateWidth) - 1:0]);

  // FIFO RDP/WRP/Level
  logic [6-1:0] fifo_cnt;  // For 32 1-bit FIFO
  logic [5-1:0] fifo_rdp, fifo_wrp;  // FIFO read pointer & write pointer
  logic [32-1:0] fifo_data;  // 32 1-bi FIFOt
  logic inc_fifo_cnt, dec_fifo_cnt;

  assign inc_fifo_cnt = (fifo_cnt < 6'h20) && entropy_ack_i;
  assign dec_fifo_cnt = (fifo_cnt != 6'h00) && read_entropy;

  always_ff @(posedge clk_ast_es_i, negedge rst_es_n) begin
    if (!rst_es_n) begin
      fifo_cnt <= 6'h00;
      fifo_rdp <= 5'h00;
      fifo_wrp <= 5'h00;
    end else if (inc_fifo_cnt && dec_fifo_cnt) begin
      fifo_rdp <= fifo_rdp + 1'b1;
      fifo_wrp <= fifo_wrp + 1'b1;
    end else if (inc_fifo_cnt) begin
      fifo_cnt <= fifo_cnt + 1'b1;
      fifo_wrp <= fifo_wrp + 1'b1;
    end else if (dec_fifo_cnt) begin
      fifo_cnt <= fifo_cnt - 1'b1;
      fifo_rdp <= fifo_rdp + 1'b1;
    end
  end

  // Request
  always_ff @(posedge clk_ast_es_i, negedge rst_es_n) begin
    if (!rst_es_n) entropy_req_o <= 1'b0;
    else if (fifo_cnt < 6'h10) entropy_req_o <= 1'b1;  // Half
    else if ((fifo_cnt == 6'h1f) && inc_fifo_cnt && ~dec_fifo_cnt) entropy_req_o <= 1'b0;  // Full
  end

  // FIFO Write
  always_ff @(posedge clk_ast_es_i, negedge rst_es_n) begin
    if (!rst_es_n) fifo_data[32 - 1:0] <= {32{1'b0}};
    else if (inc_fifo_cnt) fifo_data[fifo_wrp] <= entropy_i[0];
  end

  // FIFO Read
  wire fifo_entropy_out = fifo_data[fifo_rdp];


  // Sync to SYS clock
  logic lfsr_data_in;
  logic sync1_lfsr_data_in, sync2_lfsr_data_in;

  always_ff @(posedge clk_src_sys_i, negedge rst_src_sys_ni) begin
    if (!rst_src_sys_ni) begin
      sync1_lfsr_data_in <= 1'b0;
      sync2_lfsr_data_in <= 1'b0;
    end else begin
      sync1_lfsr_data_in <= fifo_entropy_out;
      sync2_lfsr_data_in <= sync1_lfsr_data_in;
    end
  end

  assign lfsr_data_in = sync2_lfsr_data_in;

  // prim_generic_flop_2sync #(
  //    .Width ( 1 )
  // ) entropy_sync (
  //    .clk_i ( clk_src_sys_i ),
  //    .rst_ni ( rst_src_sys_ni ),
  //    .d_i ( fifo_entropy_out ),
  //    .q_o ( lfsr_data_in )
  // );


  // Jitter
  // random 0-2000ps (upto +20% of SYS clock)
  // jitter = sys_jen ? $urandom_range(2000, 0) : 0;


endmodule  // of entropy
