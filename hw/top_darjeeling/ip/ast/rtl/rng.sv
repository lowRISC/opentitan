// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
//############################################################################
// *Name: rng
// *Module Description:  Random (bit/s) Generator (Pseudo Model)
//############################################################################

`include "prim_assert.sv"

module rng #(
  parameter int EntropyStreams = 16
) (
  input clk_i,                                // Non-Jittery Clock (TLUL)
  input rst_ni,                               // Non-Jittery Reset (TLUL)
  input clk_ast_rng_i,                        // Jittery Clock (RNG)
  input rst_ast_rng_ni,                       // Jittery Reset (RNG)
  input scan_mode_i,                          // Scan Mode
  input  entropy_src_pkg::entropy_src_hw_if_req_t rng_req_i, // request
  output entropy_src_pkg::entropy_src_hw_if_rsp_t rng_rsp_o  // response
);

///////////////////////////////////////
// RNG Bus using LFSR
///////////////////////////////////////
logic[EntropyStreams-1:0] lfsr_val;

// These LFSR parameters have been generated with
// $ ./util/design/gen-lfsr-seed.py --width 64 --seed 15513 --prefix "Rng"
localparam int RngLfsrWidth = 64;
typedef logic [RngLfsrWidth-1:0] rng_lfsr_seed_t;
typedef logic [RngLfsrWidth-1:0][$clog2(RngLfsrWidth)-1:0] rng_lfsr_perm_t;
localparam rng_lfsr_seed_t RndCnstRngLfsrSeedDefault = 64'h1d033d20eed3b14;
localparam rng_lfsr_perm_t RndCnstRngLfsrPermDefault = {
  128'h98c2c94ab5e40420ed73f6c7396cd9e1,
  256'h58c6d7435ddb2ed1f22400c53a5aaa796ef7785e120628fbabc87f0b3928550f
};

prim_lfsr #(
  .LfsrDw ( RngLfsrWidth ),
  .EntropyDw ( 1 ),
  .StateOutDw ( EntropyStreams ),
  .DefaultSeed ( RndCnstRngLfsrSeedDefault ),
  .StatePermEn ( 1'b1 ),
  .StatePerm ( RndCnstRngLfsrPermDefault ),
  .NonLinearOut ( 1'b1 ),
  .ExtSeedSVA ( 1'b0 )  // ext seed is unused
) u_rng_lfsr (
  .clk_i ( clk_i ),
  .rst_ni ( rst_ni ),
  .lfsr_en_i ( 1'b1 ),
  .seed_en_i ( 1'b0 ),
  .seed_i ( '0 ),
  .entropy_i ( 1'b0 ),
  .state_o ( lfsr_val )
);

// The digital noise source vendor IP of Earlgrey has 4 entropy streams whereas the entropy source
// vendor IP of Darjeeling has 16 entropy streams. For simplicity, this model takes 16 instead of
// just 4 LSBs of the LFSR above for Darjeeling. To remain compliant with the rate modulation
// performed in DV, the rate counter for Darjeeling is modified to count 4 times slower. Both
// models thus provide entropy at the same rate.
localparam int SRateWidth = 12;
localparam int SRateCntWidth = 14;

logic srate_rng_val;
logic [SRateWidth-1:0] srate_value;
logic [SRateCntWidth-1:0] srate_cnt;
logic srate_cnt_expired;

logic [EntropyStreams-1:0] rng_b;

`ifndef SYNTHESIS
logic [SRateWidth-1:0] dv_srate_value;
// 4-bit rng_b needs at least 5 clocks. While the limit for these min and max values is 5:500, the
// default is set to a shorter window of 32:128 to avoid large runtimes.
logic [SRateWidth-1:0] rng_srate_value_min = SRateWidth'(32);
logic [SRateWidth-1:0] rng_srate_value_max = SRateWidth'(128);

initial begin : rng_plusargs
  void'($value$plusargs("rng_srate_value_min=%0d", rng_srate_value_min));
  void'($value$plusargs("rng_srate_value_max=%0d", rng_srate_value_max));
  `ASSERT_I(DvRngSrateMinCheck, rng_srate_value_min inside {[5:500]})
  `ASSERT_I(DvRngSrateMaxCheck, rng_srate_value_max inside {[5:500]})
  `ASSERT_I(DvRngSrateBoundsCheck, rng_srate_value_max >= rng_srate_value_min)
  dv_srate_value =
      SRateWidth'($urandom_range(int'(rng_srate_value_min), int'(rng_srate_value_max)));
  void'($value$plusargs("rng_srate_value=%0d", dv_srate_value));
  `ASSERT_I(DvSrateValueCheck, dv_srate_value inside {[5:500]})
end

assign srate_value = dv_srate_value;
`else
assign srate_value = SRateWidth'(120);
`endif

logic src_busy;
assign srate_cnt_expired = (srate_cnt[SRateCntWidth-1:SRateCntWidth-SRateWidth] == srate_value);

always_ff @( posedge clk_i, negedge rst_ni ) begin
  if ( !rst_ni ) begin
    srate_cnt     <= '0;
    srate_rng_val <= 1'b0;
  end else if ( srate_cnt_expired && src_busy ) begin
    srate_rng_val <= 1'b0;
  end else if ( srate_cnt_expired ) begin
    srate_cnt     <= '0;
    srate_rng_val <= 1'b1;
  end else begin
    srate_cnt     <= srate_cnt + 1'b1;
    srate_rng_val <= 1'b0;
  end
end


////////////////////////////////////////
// Sychronize Bus & Valid to RNG Clock
////////////////////////////////////////
logic sync_rng_val, srate_rng_val_en;
logic [EntropyStreams-1:0] rng_b_ast;
logic rng_val_ast;

ast_pulse_sync u_rng_val_pulse_sync (
  .scan_mode_i ( scan_mode_i ),
  // source clock domain
  .clk_src_i ( clk_i ),
  .rst_src_ni ( rst_ni ),
  .src_pulse_i ( srate_rng_val ),
  .src_pulse_en_o ( srate_rng_val_en ),
  .src_busy_o ( src_busy ),
  // destination clock domain
  .clk_dst_i ( clk_ast_rng_i ),
  .rst_dst_ni ( rst_ast_rng_ni ),
  .dst_pulse_o ( sync_rng_val )
);

// Sample & Hold the rng_b value until the sync completes
always_ff @( posedge clk_i, negedge rst_ni ) begin
  if ( !rst_ni ) begin
    rng_b <= {EntropyStreams{1'b0}};
  end else if ( srate_rng_val_en ) begin
    rng_b <= lfsr_val[EntropyStreams-1:0];
  end
end

// Sync to RNG clock domain
always_ff @( posedge clk_ast_rng_i, negedge rst_ast_rng_ni ) begin
  if (!rst_ast_rng_ni ) begin
    rng_b_ast <= {EntropyStreams{1'b0}};
    rng_val_ast <= 1'b0;
  end else if ( sync_rng_val ) begin
    rng_b_ast <= rng_b[EntropyStreams-1:0];
    rng_val_ast <= 1'b1;
  end else begin
    rng_val_ast <= 1'b0;
  end
end

//////////////////////////////////////////////
// Conversion of model output to Darjeeling //
//////////////////////////////////////////////

// Darjeeling CDC notes:
// - The RNG model (LFSR) runs on clk_i <- clk_ast_tlul_i <- clkmgr_aon_clocks.clk_io_div4_infra
//   which is roughly 250 MHz.
// - The final rng_b_ast buffer above run on clk_ast_rng_i <- clkmgr_aon_clocks.clk_main_secure
//   which is roughly 1 GHz and the exact same clock used for CSRNG, i.e., the consumer of the
//   entropy produced here.
// As a result no further CDC is needed for this open source model. When interfacing the
// entropy source vendor IP of Darjeeling, an additional CDC might be needed. The recommendation
// is to insert the CDC before the packer FIFO/width conversion below.
logic rng_packer_wvalid, rng_packer_wready, rng_packer_rvalid, rng_packer_rready;

// rng_val_ast is always going to be high for exactly one clock cycle. The packer shall accept data
// from rng_b_ast unless it's currently full. If the packer FIFO is full, the current content of
// rng_b_ast is dropped.
assign rng_packer_wvalid = rng_val_ast & rng_packer_wready;

prim_packer_fifo #(
  .InW(EntropyStreams),
  .OutW(entropy_src_pkg::CSRNG_BUS_WIDTH),
  .ClearOnRead(1'b0)
) u_prim_packer_fifo_rng (
  .clk_i      (clk_ast_rng_i),
  .rst_ni     (rst_ast_rng_ni),
  .clr_i      (1'b0),
  .wvalid_i   (rng_packer_wvalid),
  .wdata_i    (rng_b_ast),
  .wready_o   (rng_packer_wready),
  .rvalid_o   (rng_packer_rvalid),
  .rdata_o    (rng_rsp_o.es_bits),
  .rready_i   (rng_packer_rready),
  .depth_o    ()
);

// We can forward the valid/ack even if entropy is not actually being requested. CSRNG only samples
// rng_rsp_o.es_bits when actually requesting entropy.
assign rng_rsp_o.es_ack = rng_packer_rvalid;

// Signal ready whenever entropy is being requested.
assign rng_packer_rready = rng_req_i.es_req;

// The Darjeeling entropy_src vendor IP always provides FIPS qualified entropy.
assign rng_rsp_o.es_fips = 1'b1;

endmodule : rng
