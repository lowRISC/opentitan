// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: rng
// *Module Description:  Random (bit/s) Generator
//############################################################################

module rng #(
  parameter int EntropyStreams = 4
) (
  input clk_i,
  input rst_ni,
  input vcaon_pok_i,
  input rng_en_i,
  input scan_mode_i,
  input scan_reset_ni,
  output logic [EntropyStreams-1:0] rng_b_o,
  output logic rng_val_o
);

///////////////////////////////////////
// Clock Oscilator
///////////////////////////////////////
logic clk, rng_clk_en, rng_clk;

// clock Oschilator
////////////////////////////////////////
// For FPGA, it can be replace with clk_src_aon_o/4 (200K/4=50K)
rng_osc u_rng_osc (
  .vcaon_pok_i ( vcaon_pok_i ),
  .rng_en_i ( rng_en_i ),
  .rng_clk_o ( rng_clk_o )
);  // of u_rng_osc


///////////////////////////////////////
// LFSR for Pseudo Random Numbers
///////////////////////////////////////
logic rng_rst_n;
logic[32-1:0] lfsr_val;

assign rng_rst_n = scan_mode_i ? scan_reset_ni : rst_ni && rng_en_i;

always_ff @(posedge rng_clk_o, negedge rng_rst_n ) begin
  if ( !rng_rst_n ) begin
    lfsr_val       <= 32'h0000_0001;
  end else if ( lfsr_val == {32{1'b1}} ) begin  // Skip one problematic value
    lfsr_val       <= {{31{1'b1}}, 1'b0};
  end else begin
    lfsr_val[31:1] <= lfsr_val[30:0];
    lfsr_val[0]    <= !(lfsr_val[31] ^ lfsr_val[21] ^ lfsr_val[1] ^ lfsr_val[0]);
  end
end


///////////////////////////////////////
// RNG Bus & OK
///////////////////////////////////////
logic rng_rdy;
logic [2-1:0] rng_rdy_cnt;

always_ff @( posedge rng_clk_o, negedge rng_rst_n ) begin
  if ( !rng_rst_n ) begin
    rng_rdy_cnt <= 2'b00;
  end else if ( !rng_rdy ) begin
    rng_rdy_cnt <= rng_rdy_cnt + 1'b1;
  end
end

assign rng_rdy = (rng_rdy_cnt == 2'b11);

logic [EntropyStreams-1:0] rng_b;

always_ff @( posedge rng_clk_o, negedge rng_rst_n ) begin
  if ( !rng_rst_n ) begin
    rng_b <= {EntropyStreams{1'b0}};
  end else begin
    rng_b <= lfsr_val[EntropyStreams-1:0];
  end
end


// Sync RNG OK to clk_i
logic rng_rdy_s;

always_ff @( posedge clk_i, negedge rst_ni ) begin
  if ( !rst_ni ) begin
    rng_rdy_s <= 1'b0;
    rng_val_o <= 1'b0;
  end else begin
    rng_rdy_s <= rng_rdy;
    rng_val_o <= rng_rdy_s;
  end
end

// Sync RNG Bits to clk_i
logic [EntropyStreams-1:0] rng_b_r;

always_ff @( posedge clk_i, negedge rst_ni ) begin
  if ( !rst_ni ) begin
    rng_b_r <= {EntropyStreams{1'b0}};
    rng_b_o <= {EntropyStreams{1'b0}};
  end else begin
    rng_b_r <= rng_b;
    rng_b_o <= rng_b_r;
  end
end

endmodule : rng
