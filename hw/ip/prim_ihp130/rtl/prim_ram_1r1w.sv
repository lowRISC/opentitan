// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// 1-read 1-write dual-port SRAM mapped to IHP SG13CMOS5L 2P SRAM macros.
// Port A is write-only (A_WEN=1, A_REN=0).
// Port B is read-only  (B_WEN=0, B_REN=1).
// Supported: Width=32 (single cut) and Width=36 (32 data + 4 parity bits, two cuts).
// Depth up to 1024 words.

`include "prim_assert.sv"

module prim_ram_1r1w_blackbox #(
  parameter int Width = 32,
  parameter int Depth = 128
) ();
endmodule

module prim_ram_1r1w import prim_ram_1r1w_pkg::*; #(
  parameter  int Width           = 32, // bit
  parameter  int Depth           = 128,
  parameter  int DataBitsPerMask = 1, // Number of data bits per bit of write mask
  parameter      MemInitFile     = "", // VMEM file to initialize the memory with

  localparam int Aw              = $clog2(Depth)  // derived parameter
) (
  input logic              clk_a_i,
  input logic              clk_b_i,
  input logic              rst_a_ni,
  input logic              rst_b_ni,

  // Port A can only write
  input                    a_req_i,
  input        [Aw-1:0]    a_addr_i,
  input        [Width-1:0] a_wdata_i,
  input  logic [Width-1:0] a_wmask_i,

  // Port B can only read
  input                    b_req_i,
  input        [Aw-1:0]    b_addr_i,
  output logic [Width-1:0] b_rdata_o,

  input  ram_1r1w_cfg_req_t cfg_i,
  output ram_1r1w_cfg_rsp_t cfg_o
);

  logic unused_cfg;
  assign unused_cfg = ^{rst_a_ni, rst_b_ni, cfg_i};
  assign cfg_o = RAM_1R1W_CFG_RSP_DEFAULT;

  // Width=32, Depth <= 256: RM_IHPSG13_2P_256x32_c2_bm_bist (A_ADDR[7:0])
  if (Width == 32 && Depth <= 256) begin : gen_32xle256
    logic [31:0] wdata32, bm32, rdata32;
    assign wdata32    = a_wdata_i;
    assign bm32       = a_wmask_i;
    assign b_rdata_o  = rdata32;

    RM_IHPSG13_2P_256x32_c2_bm_bist i_cut (
      .A_CLK       ( clk_a_i        ),
      .A_DLY       ( 1'b1           ),
      .A_ADDR      ( 8'(a_addr_i)   ),
      .A_BM        ( bm32           ),
      .A_MEN       ( a_req_i        ),
      .A_WEN       ( 1'b1           ),
      .A_REN       ( 1'b0           ),
      .A_DIN       ( wdata32        ),
      .A_DOUT      (                ),
      .A_BIST_CLK  ( 1'b0           ),
      .A_BIST_ADDR ( 8'd0           ),
      .A_BIST_DIN  ( 32'd0          ),
      .A_BIST_BM   ( 32'd0          ),
      .A_BIST_MEN  ( 1'b0           ),
      .A_BIST_WEN  ( 1'b0           ),
      .A_BIST_REN  ( 1'b0           ),
      .A_BIST_EN   ( 1'b0           ),
      .B_CLK       ( clk_b_i        ),
      .B_DLY       ( 1'b1           ),
      .B_ADDR      ( 8'(b_addr_i)   ),
      .B_BM        ( 32'hFFFF_FFFF  ),
      .B_MEN       ( b_req_i        ),
      .B_WEN       ( 1'b0           ),
      .B_REN       ( 1'b1           ),
      .B_DIN       ( 32'd0          ),
      .B_DOUT      ( rdata32        ),
      .B_BIST_CLK  ( 1'b0           ),
      .B_BIST_ADDR ( 8'd0           ),
      .B_BIST_DIN  ( 32'd0          ),
      .B_BIST_BM   ( 32'd0          ),
      .B_BIST_MEN  ( 1'b0           ),
      .B_BIST_WEN  ( 1'b0           ),
      .B_BIST_REN  ( 1'b0           ),
      .B_BIST_EN   ( 1'b0           )
    );

  // Width=32, Depth <= 512: RM_IHPSG13_2P_512x32_c2_bm_bist (A_ADDR[8:0])
  end else if (Width == 32 && Depth <= 512) begin : gen_32xle512
    logic [31:0] wdata32, bm32, rdata32;
    assign wdata32    = a_wdata_i;
    assign bm32       = a_wmask_i;
    assign b_rdata_o  = rdata32;

    RM_IHPSG13_2P_512x32_c2_bm_bist i_cut (
      .A_CLK       ( clk_a_i        ),
      .A_DLY       ( 1'b1           ),
      .A_ADDR      ( 9'(a_addr_i)   ),
      .A_BM        ( bm32           ),
      .A_MEN       ( a_req_i        ),
      .A_WEN       ( 1'b1           ),
      .A_REN       ( 1'b0           ),
      .A_DIN       ( wdata32        ),
      .A_DOUT      (                ),
      .A_BIST_CLK  ( 1'b0           ),
      .A_BIST_ADDR ( 9'd0           ),
      .A_BIST_DIN  ( 32'd0          ),
      .A_BIST_BM   ( 32'd0          ),
      .A_BIST_MEN  ( 1'b0           ),
      .A_BIST_WEN  ( 1'b0           ),
      .A_BIST_REN  ( 1'b0           ),
      .A_BIST_EN   ( 1'b0           ),
      .B_CLK       ( clk_b_i        ),
      .B_DLY       ( 1'b1           ),
      .B_ADDR      ( 9'(b_addr_i)   ),
      .B_BM        ( 32'hFFFF_FFFF  ),
      .B_MEN       ( b_req_i        ),
      .B_WEN       ( 1'b0           ),
      .B_REN       ( 1'b1           ),
      .B_DIN       ( 32'd0          ),
      .B_DOUT      ( rdata32        ),
      .B_BIST_CLK  ( 1'b0           ),
      .B_BIST_ADDR ( 9'd0           ),
      .B_BIST_DIN  ( 32'd0          ),
      .B_BIST_BM   ( 32'd0          ),
      .B_BIST_MEN  ( 1'b0           ),
      .B_BIST_WEN  ( 1'b0           ),
      .B_BIST_REN  ( 1'b0           ),
      .B_BIST_EN   ( 1'b0           )
    );

  // Width=32, Depth <= 1024: RM_IHPSG13_2P_1024x32_c2_bm_bist (A_ADDR[9:0])
  end else if (Width == 32 && Depth <= 1024) begin : gen_32xle1024
    logic [31:0] wdata32, bm32, rdata32;
    assign wdata32    = a_wdata_i;
    assign bm32       = a_wmask_i;
    assign b_rdata_o  = rdata32;

    RM_IHPSG13_2P_1024x32_c2_bm_bist i_cut (
      .A_CLK       ( clk_a_i        ),
      .A_DLY       ( 1'b1           ),
      .A_ADDR      ( 10'(a_addr_i)  ),
      .A_BM        ( bm32           ),
      .A_MEN       ( a_req_i        ),
      .A_WEN       ( 1'b1           ),
      .A_REN       ( 1'b0           ),
      .A_DIN       ( wdata32        ),
      .A_DOUT      (                ),
      .A_BIST_CLK  ( 1'b0           ),
      .A_BIST_ADDR ( 10'd0          ),
      .A_BIST_DIN  ( 32'd0          ),
      .A_BIST_BM   ( 32'd0          ),
      .A_BIST_MEN  ( 1'b0           ),
      .A_BIST_WEN  ( 1'b0           ),
      .A_BIST_REN  ( 1'b0           ),
      .A_BIST_EN   ( 1'b0           ),
      .B_CLK       ( clk_b_i        ),
      .B_DLY       ( 1'b1           ),
      .B_ADDR      ( 10'(b_addr_i)  ),
      .B_BM        ( 32'hFFFF_FFFF  ),
      .B_MEN       ( b_req_i        ),
      .B_WEN       ( 1'b0           ),
      .B_REN       ( 1'b1           ),
      .B_DIN       ( 32'd0          ),
      .B_DOUT      ( rdata32        ),
      .B_BIST_CLK  ( 1'b0           ),
      .B_BIST_ADDR ( 10'd0          ),
      .B_BIST_DIN  ( 32'd0          ),
      .B_BIST_BM   ( 32'd0          ),
      .B_BIST_MEN  ( 1'b0           ),
      .B_BIST_WEN  ( 1'b0           ),
      .B_BIST_REN  ( 1'b0           ),
      .B_BIST_EN   ( 1'b0           )
    );

  // Width=36, Depth <= 256: two 256x32 cuts (lo[31:0] + hi[35:32] = 4 parity bits)
  end else if (Width == 36 && Depth <= 256) begin : gen_36xle256
    logic [31:0] wdata_lo, bm_lo, rdata_lo;
    logic [31:0] wdata_hi, bm_hi, rdata_hi;
    assign wdata_lo   = a_wdata_i[31:0];
    assign bm_lo      = a_wmask_i[31:0];
    assign wdata_hi   = {28'b0, a_wdata_i[35:32]};
    assign bm_hi      = {28'b0, a_wmask_i[35:32]};
    assign b_rdata_o  = {rdata_hi[3:0], rdata_lo};

    RM_IHPSG13_2P_256x32_c2_bm_bist i_cut_lo (
      .A_CLK       ( clk_a_i        ),
      .A_DLY       ( 1'b1           ),
      .A_ADDR      ( 8'(a_addr_i)   ),
      .A_BM        ( bm_lo          ),
      .A_MEN       ( a_req_i        ),
      .A_WEN       ( 1'b1           ),
      .A_REN       ( 1'b0           ),
      .A_DIN       ( wdata_lo       ),
      .A_DOUT      (                ),
      .A_BIST_CLK  ( 1'b0           ),
      .A_BIST_ADDR ( 8'd0           ),
      .A_BIST_DIN  ( 32'd0          ),
      .A_BIST_BM   ( 32'd0          ),
      .A_BIST_MEN  ( 1'b0           ),
      .A_BIST_WEN  ( 1'b0           ),
      .A_BIST_REN  ( 1'b0           ),
      .A_BIST_EN   ( 1'b0           ),
      .B_CLK       ( clk_b_i        ),
      .B_DLY       ( 1'b1           ),
      .B_ADDR      ( 8'(b_addr_i)   ),
      .B_BM        ( 32'hFFFF_FFFF  ),
      .B_MEN       ( b_req_i        ),
      .B_WEN       ( 1'b0           ),
      .B_REN       ( 1'b1           ),
      .B_DIN       ( 32'd0          ),
      .B_DOUT      ( rdata_lo       ),
      .B_BIST_CLK  ( 1'b0           ),
      .B_BIST_ADDR ( 8'd0           ),
      .B_BIST_DIN  ( 32'd0          ),
      .B_BIST_BM   ( 32'd0          ),
      .B_BIST_MEN  ( 1'b0           ),
      .B_BIST_WEN  ( 1'b0           ),
      .B_BIST_REN  ( 1'b0           ),
      .B_BIST_EN   ( 1'b0           )
    );

    RM_IHPSG13_2P_256x32_c2_bm_bist i_cut_hi (
      .A_CLK       ( clk_a_i        ),
      .A_DLY       ( 1'b1           ),
      .A_ADDR      ( 8'(a_addr_i)   ),
      .A_BM        ( bm_hi          ),
      .A_MEN       ( a_req_i        ),
      .A_WEN       ( 1'b1           ),
      .A_REN       ( 1'b0           ),
      .A_DIN       ( wdata_hi       ),
      .A_DOUT      (                ),
      .A_BIST_CLK  ( 1'b0           ),
      .A_BIST_ADDR ( 8'd0           ),
      .A_BIST_DIN  ( 32'd0          ),
      .A_BIST_BM   ( 32'd0          ),
      .A_BIST_MEN  ( 1'b0           ),
      .A_BIST_WEN  ( 1'b0           ),
      .A_BIST_REN  ( 1'b0           ),
      .A_BIST_EN   ( 1'b0           ),
      .B_CLK       ( clk_b_i        ),
      .B_DLY       ( 1'b1           ),
      .B_ADDR      ( 8'(b_addr_i)   ),
      .B_BM        ( 32'hFFFF_FFFF  ),
      .B_MEN       ( b_req_i        ),
      .B_WEN       ( 1'b0           ),
      .B_REN       ( 1'b1           ),
      .B_DIN       ( 32'd0          ),
      .B_DOUT      ( rdata_hi       ),
      .B_BIST_CLK  ( 1'b0           ),
      .B_BIST_ADDR ( 8'd0           ),
      .B_BIST_DIN  ( 32'd0          ),
      .B_BIST_BM   ( 32'd0          ),
      .B_BIST_MEN  ( 1'b0           ),
      .B_BIST_WEN  ( 1'b0           ),
      .B_BIST_REN  ( 1'b0           ),
      .B_BIST_EN   ( 1'b0           )
    );

  // Width=36, Depth <= 512: two 512x32 cuts
  end else if (Width == 36 && Depth <= 512) begin : gen_36xle512
    logic [31:0] wdata_lo, bm_lo, rdata_lo;
    logic [31:0] wdata_hi, bm_hi, rdata_hi;
    assign wdata_lo   = a_wdata_i[31:0];
    assign bm_lo      = a_wmask_i[31:0];
    assign wdata_hi   = {28'b0, a_wdata_i[35:32]};
    assign bm_hi      = {28'b0, a_wmask_i[35:32]};
    assign b_rdata_o  = {rdata_hi[3:0], rdata_lo};

    RM_IHPSG13_2P_512x32_c2_bm_bist i_cut_lo (
      .A_CLK       ( clk_a_i        ),
      .A_DLY       ( 1'b1           ),
      .A_ADDR      ( 9'(a_addr_i)   ),
      .A_BM        ( bm_lo          ),
      .A_MEN       ( a_req_i        ),
      .A_WEN       ( 1'b1           ),
      .A_REN       ( 1'b0           ),
      .A_DIN       ( wdata_lo       ),
      .A_DOUT      (                ),
      .A_BIST_CLK  ( 1'b0           ),
      .A_BIST_ADDR ( 9'd0           ),
      .A_BIST_DIN  ( 32'd0          ),
      .A_BIST_BM   ( 32'd0          ),
      .A_BIST_MEN  ( 1'b0           ),
      .A_BIST_WEN  ( 1'b0           ),
      .A_BIST_REN  ( 1'b0           ),
      .A_BIST_EN   ( 1'b0           ),
      .B_CLK       ( clk_b_i        ),
      .B_DLY       ( 1'b1           ),
      .B_ADDR      ( 9'(b_addr_i)   ),
      .B_BM        ( 32'hFFFF_FFFF  ),
      .B_MEN       ( b_req_i        ),
      .B_WEN       ( 1'b0           ),
      .B_REN       ( 1'b1           ),
      .B_DIN       ( 32'd0          ),
      .B_DOUT      ( rdata_lo       ),
      .B_BIST_CLK  ( 1'b0           ),
      .B_BIST_ADDR ( 9'd0           ),
      .B_BIST_DIN  ( 32'd0          ),
      .B_BIST_BM   ( 32'd0          ),
      .B_BIST_MEN  ( 1'b0           ),
      .B_BIST_WEN  ( 1'b0           ),
      .B_BIST_REN  ( 1'b0           ),
      .B_BIST_EN   ( 1'b0           )
    );

    RM_IHPSG13_2P_512x32_c2_bm_bist i_cut_hi (
      .A_CLK       ( clk_a_i        ),
      .A_DLY       ( 1'b1           ),
      .A_ADDR      ( 9'(a_addr_i)   ),
      .A_BM        ( bm_hi          ),
      .A_MEN       ( a_req_i        ),
      .A_WEN       ( 1'b1           ),
      .A_REN       ( 1'b0           ),
      .A_DIN       ( wdata_hi       ),
      .A_DOUT      (                ),
      .A_BIST_CLK  ( 1'b0           ),
      .A_BIST_ADDR ( 9'd0           ),
      .A_BIST_DIN  ( 32'd0          ),
      .A_BIST_BM   ( 32'd0          ),
      .A_BIST_MEN  ( 1'b0           ),
      .A_BIST_WEN  ( 1'b0           ),
      .A_BIST_REN  ( 1'b0           ),
      .A_BIST_EN   ( 1'b0           ),
      .B_CLK       ( clk_b_i        ),
      .B_DLY       ( 1'b1           ),
      .B_ADDR      ( 9'(b_addr_i)   ),
      .B_BM        ( 32'hFFFF_FFFF  ),
      .B_MEN       ( b_req_i        ),
      .B_WEN       ( 1'b0           ),
      .B_REN       ( 1'b1           ),
      .B_DIN       ( 32'd0          ),
      .B_DOUT      ( rdata_hi       ),
      .B_BIST_CLK  ( 1'b0           ),
      .B_BIST_ADDR ( 9'd0           ),
      .B_BIST_DIN  ( 32'd0          ),
      .B_BIST_BM   ( 32'd0          ),
      .B_BIST_MEN  ( 1'b0           ),
      .B_BIST_WEN  ( 1'b0           ),
      .B_BIST_REN  ( 1'b0           ),
      .B_BIST_EN   ( 1'b0           )
    );

  // Width=36, Depth <= 1024: two 1024x32 cuts
  end else if (Width == 36 && Depth <= 1024) begin : gen_36xle1024
    logic [31:0] wdata_lo, bm_lo, rdata_lo;
    logic [31:0] wdata_hi, bm_hi, rdata_hi;
    assign wdata_lo   = a_wdata_i[31:0];
    assign bm_lo      = a_wmask_i[31:0];
    assign wdata_hi   = {28'b0, a_wdata_i[35:32]};
    assign bm_hi      = {28'b0, a_wmask_i[35:32]};
    assign b_rdata_o  = {rdata_hi[3:0], rdata_lo};

    RM_IHPSG13_2P_1024x32_c2_bm_bist i_cut_lo (
      .A_CLK       ( clk_a_i        ),
      .A_DLY       ( 1'b1           ),
      .A_ADDR      ( 10'(a_addr_i)  ),
      .A_BM        ( bm_lo          ),
      .A_MEN       ( a_req_i        ),
      .A_WEN       ( 1'b1           ),
      .A_REN       ( 1'b0           ),
      .A_DIN       ( wdata_lo       ),
      .A_DOUT      (                ),
      .A_BIST_CLK  ( 1'b0           ),
      .A_BIST_ADDR ( 10'd0          ),
      .A_BIST_DIN  ( 32'd0          ),
      .A_BIST_BM   ( 32'd0          ),
      .A_BIST_MEN  ( 1'b0           ),
      .A_BIST_WEN  ( 1'b0           ),
      .A_BIST_REN  ( 1'b0           ),
      .A_BIST_EN   ( 1'b0           ),
      .B_CLK       ( clk_b_i        ),
      .B_DLY       ( 1'b1           ),
      .B_ADDR      ( 10'(b_addr_i)  ),
      .B_BM        ( 32'hFFFF_FFFF  ),
      .B_MEN       ( b_req_i        ),
      .B_WEN       ( 1'b0           ),
      .B_REN       ( 1'b1           ),
      .B_DIN       ( 32'd0          ),
      .B_DOUT      ( rdata_lo       ),
      .B_BIST_CLK  ( 1'b0           ),
      .B_BIST_ADDR ( 10'd0          ),
      .B_BIST_DIN  ( 32'd0          ),
      .B_BIST_BM   ( 32'd0          ),
      .B_BIST_MEN  ( 1'b0           ),
      .B_BIST_WEN  ( 1'b0           ),
      .B_BIST_REN  ( 1'b0           ),
      .B_BIST_EN   ( 1'b0           )
    );

    RM_IHPSG13_2P_1024x32_c2_bm_bist i_cut_hi (
      .A_CLK       ( clk_a_i        ),
      .A_DLY       ( 1'b1           ),
      .A_ADDR      ( 10'(a_addr_i)  ),
      .A_BM        ( bm_hi          ),
      .A_MEN       ( a_req_i        ),
      .A_WEN       ( 1'b1           ),
      .A_REN       ( 1'b0           ),
      .A_DIN       ( wdata_hi       ),
      .A_DOUT      (                ),
      .A_BIST_CLK  ( 1'b0           ),
      .A_BIST_ADDR ( 10'd0          ),
      .A_BIST_DIN  ( 32'd0          ),
      .A_BIST_BM   ( 32'd0          ),
      .A_BIST_MEN  ( 1'b0           ),
      .A_BIST_WEN  ( 1'b0           ),
      .A_BIST_REN  ( 1'b0           ),
      .A_BIST_EN   ( 1'b0           ),
      .B_CLK       ( clk_b_i        ),
      .B_DLY       ( 1'b1           ),
      .B_ADDR      ( 10'(b_addr_i)  ),
      .B_BM        ( 32'hFFFF_FFFF  ),
      .B_MEN       ( b_req_i        ),
      .B_WEN       ( 1'b0           ),
      .B_REN       ( 1'b1           ),
      .B_DIN       ( 32'd0          ),
      .B_DOUT      ( rdata_hi       ),
      .B_BIST_CLK  ( 1'b0           ),
      .B_BIST_ADDR ( 10'd0          ),
      .B_BIST_DIN  ( 32'd0          ),
      .B_BIST_BM   ( 32'd0          ),
      .B_BIST_MEN  ( 1'b0           ),
      .B_BIST_WEN  ( 1'b0           ),
      .B_BIST_REN  ( 1'b0           ),
      .B_BIST_EN   ( 1'b0           )
    );

  end else begin : gen_blackbox
    `ifndef SYNTHESIS
      initial $fatal("No prim_ram_1r1w for %m: Width=%0d Depth=%0d", Width, Depth);
    `endif
    assign b_rdata_o = '0;
    `ifdef SYNTHESIS
      (* dont_touch = "true" *)
      prim_ram_1r1w_blackbox #(
        .Width (Width),
        .Depth (Depth)
      ) i_sram_blackbox ();
    `endif
  end

endmodule
