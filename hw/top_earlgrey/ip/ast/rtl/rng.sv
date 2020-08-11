// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: rng
// *Module Description:  Random (bit/s) Generator
//
//############################################################################
`timescale 1ns / 1ps

module rng #(
    parameter int EntropyStreams = 4
) (
    output logic                      rng_ok_o,
    output logic [EntropyStreams-1:0] rng_b_o,
    input                             rng_en_i,
    input                             clk_i,
    input                             rst_ni
);

  ///////////////////////////////////////
  // Clock Oscilator
  ///////////////////////////////////////
  logic clk, rng_clk_en;

  // Behavioral Model
  // For FPGA, it can be replace with clk_src_aon_o/4 (200K/4=50K)
  rng_osc i_rng_osc (
      /*I*/.en_i    (rng_en_i),
      /*O*/.clk_o   (clk),
      /*O*/.clk_en_o(rng_clk_en)
  );

  logic rng_clk, clk_en;

  always_ff @(posedge clk, negedge rst_ni) begin
    if (!rst_ni) clk_en <= 1'b0;
    else clk_en <= rng_clk_en;
  end

  assign rng_clk = clk_en ? ~clk : 1'b0;


  ///////////////////////////////////////
  // LFSR for Pseudo Random Numbers
  ///////////////////////////////////////
  logic rng_rst_n;
  logic [32-1:0] lfsr_val;

  assign rng_rst_n = rst_ni && rng_en_i;

  always_ff @(posedge rng_clk, negedge rng_rst_n) begin
    if (!rng_rst_n) begin
      lfsr_val <= 32'h1234_5678;
    end else begin
      lfsr_val[31:1] <= lfsr_val[30:0];
      lfsr_val[0] <= ~(lfsr_val[31] ^ lfsr_val[21] ^ lfsr_val[1] ^ lfsr_val[0]);
    end
  end


  ///////////////////////////////////////
  // RNG Bus & OK
  ///////////////////////////////////////
  logic rng_rdy;
  logic [2-1:0] rng_rdy_cnt;

  always_ff @(posedge rng_clk, negedge rng_rst_n) begin
    if (!rng_rst_n) rng_rdy_cnt <= 2'b00;
    else if (!rng_rdy) rng_rdy_cnt <= rng_rdy_cnt + 1'b1;
  end

  assign rng_rdy = (rng_rdy_cnt == 2'b11);

  logic [EntropyStreams-1:0] rng_b;

  always_ff @(posedge rng_clk, negedge rng_rst_n) begin
    if (!rng_rst_n) rng_b <= {EntropyStreams{1'b0}};
    else rng_b <= lfsr_val[EntropyStreams - 1:0];
  end

  // RNG OK!
  logic rng_ok_r;

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      rng_ok_r <= 1'b0;
      rng_ok_o <= 1'b0;
    end else begin
      rng_ok_r <= rng_rdy;
      rng_ok_o <= rng_ok_r;
    end
  end

  // Sync RNG Bits to clk_i
  logic [EntropyStreams-1:0] rng_b_r;

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      rng_b_r <= {EntropyStreams{1'b0}};
      rng_b_o <= {EntropyStreams{1'b0}};
    end else begin
      rng_b_r <= rng_b;
      rng_b_o <= rng_b_r;
    end
  end


endmodule  // of rng
