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
  input clk_i,                                // Non-Jittery Clock (TLUL)
  input rst_ni,                               // Non-Jittery Reset (TLUL)
  input clk_ast_rng_i,                        // Jittery Clock (RNG)
  input rst_ast_rng_ni,                       // Jittery Reset (RNG)
  input rng_en_i,                             // RNG Enable
  input rng_fips_i,                           // RNG FIPS Enable
  input scan_mode_i,                          // Scan Mode
  output logic [EntropyStreams-1:0] rng_b_o,  // RNG Bus/Bits Output
  output logic rng_val_o                      // RNG Bus/Bits Valid
);

///////////////////////////////////////
// RNG Bus using LFSR
///////////////////////////////////////
logic rst_n;
logic[32-1:0] lfsr_val;

assign rst_n = scan_mode_i ? rst_ni : rst_ni && rng_en_i;

always_ff @(posedge clk_i, negedge rst_n ) begin
  if ( !rst_n ) begin
    lfsr_val       <= 32'h0000_0001;
  end else if ( lfsr_val == {32{1'b1}} ) begin  // Skip one problematic value
    lfsr_val       <= {{31{1'b1}}, 1'b0};
  end else begin
    lfsr_val[31:1] <= lfsr_val[30:0];
    lfsr_val[0]    <= !(lfsr_val[31] ^ lfsr_val[21] ^ lfsr_val[1] ^ lfsr_val[0]);
  end
end

logic srate_rng_val;
logic [12-1:0] srate_cnt, srate_value;
logic [EntropyStreams-1:0] rng_b;

assign srate_value = 12'd120;

always_ff @( posedge clk_i, negedge rst_n ) begin
  if ( !rst_n ) begin
    srate_cnt     <= 12'h000;
    srate_rng_val <= 1'b0;
  end else if ( srate_cnt == srate_value ) begin
    srate_cnt     <= 12'h000;
    srate_rng_val <= 1'b1;
  end else begin
    srate_cnt     <= srate_cnt + 1'b1;
    srate_rng_val <= 1'b0;
  end
end

always_ff @( posedge clk_i, negedge rst_n ) begin
  if ( !rst_n ) begin
    rng_b <= {EntropyStreams{1'b0}};
  end else if ( srate_rng_val ) begin
    rng_b <= lfsr_val[EntropyStreams-1:0];
  end
end


////////////////////////////////////////
// Sychronize Bus & Valid to RNG Clock
////////////////////////////////////////
logic sync_rng_val;

prim_pulse_sync u_rng_val_pulse_sync (
  // source clock domain
  .clk_src_i ( clk_i ),
  .rst_src_ni ( rst_n ),
  .src_pulse_i ( srate_rng_val ),
  // destination clock domain
  .clk_dst_i ( clk_ast_rng_i ),
  .rst_dst_ni ( rst_ast_rng_ni ),
  .dst_pulse_o ( sync_rng_val )
);

always_ff @( posedge clk_ast_rng_i, negedge rst_ast_rng_ni ) begin
  if (!rst_ast_rng_ni ) begin
    rng_b_o <= {EntropyStreams{1'b0}};
    rng_val_o <= 1'b0;
  end else if ( sync_rng_val ) begin
    rng_b_o <= rng_b[EntropyStreams-1:0];
    rng_val_o <= 1'b1;
  end else begin
    rng_val_o <= 1'b0;
  end
end

endmodule : rng
