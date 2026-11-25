// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Single-port SRAM mapped to IHP SG13CMOS5L 1P SRAM macros and synthetic RRAM/OTP macros.
// Each supported Width/Depth combination has its own branch below.

`include "prim_assert.sv"

// This module is used when it can not be mapped to any of the following
// IHP130 SRAM macros.
module prim_ram_1p_blackbox #(
  parameter int Width           = 32,
  parameter int Depth           = 128,
  parameter int DataBitsPerMask = 1
) ();
endmodule

module prim_ram_1p import prim_ram_1p_pkg::*; #(
  parameter  int Width           = 32, // bit
  parameter  int Depth           = 128,
  parameter  int DataBitsPerMask = 1, // Number of data bits per bit of write mask
  parameter      MemInitFile     = "", // VMEM file to initialize the memory with

  localparam int Aw              = $clog2(Depth)  // derived parameter
) (
  input  logic             clk_i,
  input  logic             rst_ni,

  input  logic             req_i,
  input  logic             write_i,
  input  logic [Aw-1:0]    addr_i,
  input  logic [Width-1:0] wdata_i,
  input  logic [Width-1:0] wmask_i,
  output logic [Width-1:0] rdata_o, // Read data. Data is returned one cycle after req_i is high.
  input  ram_1p_cfg_req_t  cfg_i,
  output ram_1p_cfg_rsp_t  cfg_o
);

  logic unused_signals;
  assign unused_signals = ^{rst_ni, cfg_i};
  assign cfg_o = RAM_1P_CFG_RSP_DEFAULT;

  // Width 32 and Depth 512 for usbdev
  if (Depth == 512 && Width == 32) begin : gen_512x32
    logic [31:0] wdata32, rdata32, bm32;

    assign rdata_o = rdata32;
    assign wdata32 = wdata_i;
    assign bm32    = wmask_i;

    RM_IHPSG13_1P_512x32_c2_bm_bist i_cut (
      .A_CLK        ( clk_i       ),
      .A_DLY        ( 1'b1        ),
      .A_ADDR       ( addr_i[8:0] ),
      .A_BM         ( bm32        ),
      .A_MEN        ( req_i       ),
      .A_WEN        ( write_i     ),
      .A_REN        ( ~write_i    ),
      .A_DIN        ( wdata32     ),
      .A_DOUT       ( rdata32     ),
      .A_BIST_CLK   (  1'b0       ),
      .A_BIST_ADDR  (  9'd0       ),
      .A_BIST_DIN   ( 32'd0       ),
      .A_BIST_BM    ( 32'd0       ),
      .A_BIST_MEN   (  1'b0       ),
      .A_BIST_WEN   (  1'b0       ),
      .A_BIST_REN   (  1'b0       ),
      .A_BIST_EN    (  1'b0       )
    );

  // Width 39 and Depth 9728 = 9x1024 + 512 words for sram_ctrl_meta.
  end else if (Depth == 9728 && Width == 39) begin : gen_9728x39
    logic [31:0] wdata32, bm32;
    logic [7:0]  wdata8,  bm8;
    logic [31:0] rdata32 [10];
    logic [7:0]  rdata8  [10];
    logic [3:0]  bank_sel_d, bank_sel_q;  // 4 bits for banks 0-9

    assign wdata32  = wdata_i[31:0];
    assign bm32     = wmask_i[31:0];
    assign wdata8   = {1'b0, wdata_i[38:32]};
    assign bm8      = {1'b0, wmask_i[38:32]};
    assign bank_sel_d = 4'(addr_i[13:10]);

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni)               bank_sel_q <= '0;
      else if (req_i & ~write_i) bank_sel_q <= bank_sel_d;
    end

    assign rdata_o = {rdata8[bank_sel_q][6:0], rdata32[bank_sel_q]};

    // Banks 0-8: 1024-word depth
    for (genvar b = 0; b < 9; b++) begin : gen_banks_1024
      logic bank_en;
      assign bank_en = req_i & (bank_sel_d == 4'(b));

      RM_IHPSG13_1P_1024x32_c2_bm_bist i_cut_lo (
        .A_CLK        ( clk_i        ),
        .A_DLY        ( 1'b1         ),
        .A_ADDR       ( addr_i[9:0]  ),
        .A_BM         ( bm32         ),
        .A_MEN        ( bank_en      ),
        .A_WEN        ( write_i      ),
        .A_REN        ( ~write_i     ),
        .A_DIN        ( wdata32      ),
        .A_DOUT       ( rdata32[b]   ),
        .A_BIST_CLK   ( 1'b0         ),
        .A_BIST_ADDR  ( 10'd0        ),
        .A_BIST_DIN   ( 32'd0        ),
        .A_BIST_BM    ( 32'd0        ),
        .A_BIST_MEN   ( 1'b0         ),
        .A_BIST_WEN   ( 1'b0         ),
        .A_BIST_REN   ( 1'b0         ),
        .A_BIST_EN    ( 1'b0         )
      );

      RM_IHPSG13_1P_1024x8_c2_bm_bist i_cut_hi (
        .A_CLK        ( clk_i        ),
        .A_DLY        ( 1'b1         ),
        .A_ADDR       ( addr_i[9:0]  ),
        .A_BM         ( bm8          ),
        .A_MEN        ( bank_en      ),
        .A_WEN        ( write_i      ),
        .A_REN        ( ~write_i     ),
        .A_DIN        ( wdata8       ),
        .A_DOUT       ( rdata8[b]    ),
        .A_BIST_CLK   ( 1'b0         ),
        .A_BIST_ADDR  ( 10'd0        ),
        .A_BIST_DIN   ( 8'd0         ),
        .A_BIST_BM    ( 8'd0         ),
        .A_BIST_MEN   ( 1'b0         ),
        .A_BIST_WEN   ( 1'b0         ),
        .A_BIST_REN   ( 1'b0         ),
        .A_BIST_EN    ( 1'b0         )
      );
    end

    // Bank 9: 512-word depth
    begin : gen_bank9_512
      logic bank9_en;
      assign bank9_en = req_i & (bank_sel_d == 4'd9);

      RM_IHPSG13_1P_512x32_c2_bm_bist i_cut_lo (
        .A_CLK        ( clk_i        ),
        .A_DLY        ( 1'b1         ),
        .A_ADDR       ( addr_i[8:0]  ),
        .A_BM         ( bm32         ),
        .A_MEN        ( bank9_en     ),
        .A_WEN        ( write_i      ),
        .A_REN        ( ~write_i     ),
        .A_DIN        ( wdata32      ),
        .A_DOUT       ( rdata32[9]   ),
        .A_BIST_CLK   ( 1'b0         ),
        .A_BIST_ADDR  ( 9'd0         ),
        .A_BIST_DIN   ( 32'd0        ),
        .A_BIST_BM    ( 32'd0        ),
        .A_BIST_MEN   ( 1'b0         ),
        .A_BIST_WEN   ( 1'b0         ),
        .A_BIST_REN   ( 1'b0         ),
        .A_BIST_EN    ( 1'b0         )
      );

      // The IHP PDK ships 512x8 only in the c3 variant.
      RM_IHPSG13_1P_512x8_c3_bm_bist i_cut_hi (
        .A_CLK        ( clk_i        ),
        .A_DLY        ( 1'b1         ),
        .A_ADDR       ( addr_i[8:0]  ),
        .A_BM         ( bm8          ),
        .A_MEN        ( bank9_en     ),
        .A_WEN        ( write_i      ),
        .A_REN        ( ~write_i     ),
        .A_DIN        ( wdata8       ),
        .A_DOUT       ( rdata8[9]    ),
        .A_BIST_CLK   ( 1'b0         ),
        .A_BIST_ADDR  ( 9'd0         ),
        .A_BIST_DIN   ( 8'd0         ),
        .A_BIST_BM    ( 8'd0         ),
        .A_BIST_MEN   ( 1'b0         ),
        .A_BIST_WEN   ( 1'b0         ),
        .A_BIST_REN   ( 1'b0         ),
        .A_BIST_EN    ( 1'b0         )
      );
    end

  // Width 39
  // Depth 1024 = 1x1024 words for sram_ctrl_ret
  // Depth 4096 = 4x1024 words for obtn imem
  // Depth 16384 = 16x1024 words for sram_ctrl_sec
  // Depth 32768 = 32x1024 words for sram_ctrl_main
  end else if (Width == 39 &&(Depth % 1024 == 0)) begin : gen_Nx39

    localparam int unsigned NumBanks = (Depth + 32'd1023) / 32'd1024;
    localparam int unsigned BankSelW = (NumBanks > 32'd1) ? $clog2(NumBanks) : 32'd1;

    logic [31:0]          wdata32, bm32;
    logic [7:0]           wdata8,  bm8;
    logic [31:0]          rdata32 [NumBanks];
    logic [7:0]           rdata8  [NumBanks];
    logic [BankSelW-1:0]  bank_sel_d, bank_sel_q;

    assign wdata32 = wdata_i[31:0];
    assign bm32    = wmask_i[31:0];
    assign wdata8  = {1'b0, wdata_i[38:32]};
    assign bm8     = {1'b0, wmask_i[38:32]};

    if (NumBanks == 1) begin : gen_bank_sel_const
      assign bank_sel_d = '0;
    end else begin : gen_bank_sel_addr
      assign bank_sel_d = BankSelW'(addr_i[Aw-1:10]);
    end

    if (NumBanks == 1) begin : gen_bank_sel_reg_const
      assign bank_sel_q = '0;
    end else begin : gen_bank_sel_reg
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni)               bank_sel_q <= '0;
        else if (req_i & ~write_i) bank_sel_q <= bank_sel_d;
      end
    end

    assign rdata_o = {rdata8[bank_sel_q][6:0], rdata32[bank_sel_q]};

    for (genvar b = 0; b < int'(NumBanks); b++) begin : gen_banks
      logic bank_en;
      assign bank_en = (NumBanks == 1) ? req_i :
                       req_i & (bank_sel_d == BankSelW'(unsigned'(b)));

      RM_IHPSG13_1P_1024x32_c2_bm_bist i_cut_lo (
        .A_CLK        ( clk_i        ),
        .A_DLY        ( 1'b1         ),
        .A_ADDR       ( addr_i[9:0]  ),
        .A_BM         ( bm32         ),
        .A_MEN        ( bank_en      ),
        .A_WEN        ( write_i      ),
        .A_REN        ( ~write_i     ),
        .A_DIN        ( wdata32      ),
        .A_DOUT       ( rdata32[b]   ),
        .A_BIST_CLK   ( 1'b0         ),
        .A_BIST_ADDR  ( 10'd0        ),
        .A_BIST_DIN   ( 32'd0        ),
        .A_BIST_BM    ( 32'd0        ),
        .A_BIST_MEN   ( 1'b0         ),
        .A_BIST_WEN   ( 1'b0         ),
        .A_BIST_REN   ( 1'b0         ),
        .A_BIST_EN    ( 1'b0         )
      );

      RM_IHPSG13_1P_1024x8_c2_bm_bist i_cut_hi (
        .A_CLK        ( clk_i        ),
        .A_DLY        ( 1'b1         ),
        .A_ADDR       ( addr_i[9:0]  ),
        .A_BM         ( bm8          ),
        .A_MEN        ( bank_en      ),
        .A_WEN        ( write_i      ),
        .A_REN        ( ~write_i     ),
        .A_DIN        ( wdata8       ),
        .A_DOUT       ( rdata8[b]    ),
        .A_BIST_CLK   ( 1'b0         ),
        .A_BIST_ADDR  ( 10'd0        ),
        .A_BIST_DIN   ( 8'd0         ),
        .A_BIST_BM    ( 8'd0         ),
        .A_BIST_MEN   ( 1'b0         ),
        .A_BIST_WEN   ( 1'b0         ),
        .A_BIST_REN   ( 1'b0         ),
        .A_BIST_EN    ( 1'b0         )
      );
    end

  // Width 13 and Depth 464 for i2c
  end else if (Depth == 464 && Width == 13) begin : gen_464x13
    logic [15:0] wdata16, bm16, rdata16;

    assign wdata16  = {3'b0, wdata_i[12:0]};
    assign bm16     = {3'b0, wmask_i[12:0]};
    assign rdata_o  = rdata16[12:0];

    RM_IHPSG13_1P_512x16_c2_bm_bist i_cut (
      .A_CLK        ( clk_i        ),
      .A_DLY        ( 1'b1         ),
      .A_ADDR       ( addr_i[8:0]  ),
      .A_BM         ( bm16         ),
      .A_MEN        ( req_i        ),
      .A_WEN        ( write_i      ),
      .A_REN        ( ~write_i     ),
      .A_DIN        ( wdata16      ),
      .A_DOUT       ( rdata16      ),
      .A_BIST_CLK   ( 1'b0         ),
      .A_BIST_ADDR  ( 9'd0         ),
      .A_BIST_DIN   ( 16'd0        ),
      .A_BIST_BM    ( 16'd0        ),
      .A_BIST_MEN   ( 1'b0         ),
      .A_BIST_WEN   ( 1'b0         ),
      .A_BIST_REN   ( 1'b0         ),
      .A_BIST_EN    ( 1'b0         )
    );


  // Width 28 and Depth 256 for Ibex ICache tag
  end else if (Depth == 256 && Width == 28) begin : gen_256x28
    logic [31:0] wdata32, bm32, rdata32;

    assign wdata32  = {4'b0, wdata_i[27:0]};
    assign bm32     = {4'b0, wmask_i[27:0]};
    assign rdata_o  = rdata32[27:0];

    RM_IHPSG13_1P_256x32_c2_bm_bist i_cut (
      .A_CLK        ( clk_i        ),
      .A_DLY        ( 1'b1         ),
      .A_ADDR       ( addr_i[7:0]  ),
      .A_BM         ( bm32         ),
      .A_MEN        ( req_i        ),
      .A_WEN        ( write_i      ),
      .A_REN        ( ~write_i     ),
      .A_DIN        ( wdata32      ),
      .A_DOUT       ( rdata32      ),
      .A_BIST_CLK   ( 1'b0         ),
      .A_BIST_ADDR  ( 8'd0         ),
      .A_BIST_DIN   ( 32'd0        ),
      .A_BIST_BM    ( 32'd0        ),
      .A_BIST_MEN   ( 1'b0         ),
      .A_BIST_WEN   ( 1'b0         ),
      .A_BIST_REN   ( 1'b0         ),
      .A_BIST_EN    ( 1'b0         )
    );


  // Width 78 and Depth 256 for Ibex ICache data
  end else if (Depth == 256 && Width == 78) begin : gen_256x78
    logic [63:0] wdata64, bm64, rdata64;
    logic [15:0] wdata16, bm16, rdata16;

    assign wdata64  = wdata_i[63:0];
    assign bm64     = wmask_i[63:0];
    assign wdata16  = {2'b0, wdata_i[77:64]};
    assign bm16     = {2'b0, wmask_i[77:64]};
    assign rdata_o  = {rdata16[13:0], rdata64};

    RM_IHPSG13_1P_256x64_c2_bm_bist i_cut_lo (
      .A_CLK        ( clk_i        ),
      .A_DLY        ( 1'b1         ),
      .A_ADDR       ( addr_i[7:0]  ),
      .A_BM         ( bm64         ),
      .A_MEN        ( req_i        ),
      .A_WEN        ( write_i      ),
      .A_REN        ( ~write_i     ),
      .A_DIN        ( wdata64      ),
      .A_DOUT       ( rdata64      ),
      .A_BIST_CLK   ( 1'b0         ),
      .A_BIST_ADDR  ( 8'd0         ),
      .A_BIST_DIN   ( 64'd0        ),
      .A_BIST_BM    ( 64'd0        ),
      .A_BIST_MEN   ( 1'b0         ),
      .A_BIST_WEN   ( 1'b0         ),
      .A_BIST_REN   ( 1'b0         ),
      .A_BIST_EN    ( 1'b0         )
    );

    RM_IHPSG13_1P_256x16_c2_bm_bist i_cut_hi (
      .A_CLK        ( clk_i        ),
      .A_DLY        ( 1'b1         ),
      .A_ADDR       ( addr_i[7:0]  ),
      .A_BM         ( bm16         ),
      .A_MEN        ( req_i        ),
      .A_WEN        ( write_i      ),
      .A_REN        ( ~write_i     ),
      .A_DIN        ( wdata16      ),
      .A_DOUT       ( rdata16      ),
      .A_BIST_CLK   ( 1'b0         ),
      .A_BIST_ADDR  ( 8'd0         ),
      .A_BIST_DIN   ( 16'd0        ),
      .A_BIST_BM    ( 16'd0        ),
      .A_BIST_MEN   ( 1'b0         ),
      .A_BIST_WEN   ( 1'b0         ),
      .A_BIST_REN   ( 1'b0         ),
      .A_BIST_EN    ( 1'b0         )
    );

  // Width 312 and Depth 1024 for otbn dmem
  end else if (Depth == 1024 && Width == 312) begin : gen_1024x312
    logic [63:0] wdata64 [4], bm64 [4], rdata64 [4];
    logic [31:0] wdata32, bm32, rdata32;
    logic [15:0] wdata16, bm16, rdata16;
    logic [7:0]  wdata8,  bm8,  rdata8;

    assign wdata64[0] = wdata_i[63:0];
    assign wdata64[1] = wdata_i[127:64];
    assign wdata64[2] = wdata_i[191:128];
    assign wdata64[3] = wdata_i[255:192];
    assign wdata32    = wdata_i[287:256];
    assign wdata16    = wdata_i[303:288];
    assign wdata8     = wdata_i[311:304];

    assign bm64[0]    = wmask_i[63:0];
    assign bm64[1]    = wmask_i[127:64];
    assign bm64[2]    = wmask_i[191:128];
    assign bm64[3]    = wmask_i[255:192];
    assign bm32       = wmask_i[287:256];
    assign bm16       = wmask_i[303:288];
    assign bm8        = wmask_i[311:304];

    assign rdata_o = {rdata8, rdata16, rdata32,
                      rdata64[3], rdata64[2], rdata64[1], rdata64[0]};

    for (genvar c = 0; c < 4; c++) begin : gen_cuts_64
      RM_IHPSG13_1P_1024x64_c2_bm_bist i_cut_64 (
        .A_CLK       ( clk_i        ),
        .A_DLY       ( 1'b1         ),
        .A_ADDR      ( addr_i[9:0]  ),
        .A_BM        ( bm64[c]      ),
        .A_MEN       ( req_i        ),
        .A_WEN       ( write_i      ),
        .A_REN       ( ~write_i     ),
        .A_DIN       ( wdata64[c]   ),
        .A_DOUT      ( rdata64[c]   ),
        .A_BIST_CLK  ( 1'b0         ),
        .A_BIST_ADDR ( 10'd0        ),
        .A_BIST_DIN  ( 64'd0        ),
        .A_BIST_BM   ( 64'd0        ),
        .A_BIST_MEN  ( 1'b0         ),
        .A_BIST_WEN  ( 1'b0         ),
        .A_BIST_REN  ( 1'b0         ),
        .A_BIST_EN   ( 1'b0         )
      );
    end

    RM_IHPSG13_1P_1024x32_c2_bm_bist i_cut_32 (
      .A_CLK       ( clk_i        ),
      .A_DLY       ( 1'b1         ),
      .A_ADDR      ( addr_i[9:0]  ),
      .A_BM        ( bm32         ),
      .A_MEN       ( req_i        ),
      .A_WEN       ( write_i      ),
      .A_REN       ( ~write_i     ),
      .A_DIN       ( wdata32      ),
      .A_DOUT      ( rdata32      ),
      .A_BIST_CLK  ( 1'b0         ),
      .A_BIST_ADDR ( 10'd0        ),
      .A_BIST_DIN  ( 32'd0        ),
      .A_BIST_BM   ( 32'd0        ),
      .A_BIST_MEN  ( 1'b0         ),
      .A_BIST_WEN  ( 1'b0         ),
      .A_BIST_REN  ( 1'b0         ),
      .A_BIST_EN   ( 1'b0         )
    );

    RM_IHPSG13_1P_1024x16_c2_bm_bist i_cut_16 (
      .A_CLK       ( clk_i        ),
      .A_DLY       ( 1'b1         ),
      .A_ADDR      ( addr_i[9:0]  ),
      .A_BM        ( bm16         ),
      .A_MEN       ( req_i        ),
      .A_WEN       ( write_i      ),
      .A_REN       ( ~write_i     ),
      .A_DIN       ( wdata16      ),
      .A_DOUT      ( rdata16      ),
      .A_BIST_CLK  ( 1'b0         ),
      .A_BIST_ADDR ( 10'd0        ),
      .A_BIST_DIN  ( 16'd0        ),
      .A_BIST_BM   ( 16'd0        ),
      .A_BIST_MEN  ( 1'b0         ),
      .A_BIST_WEN  ( 1'b0         ),
      .A_BIST_REN  ( 1'b0         ),
      .A_BIST_EN   ( 1'b0         )
    );

    RM_IHPSG13_1P_1024x8_c2_bm_bist i_cut_8 (
      .A_CLK       ( clk_i        ),
      .A_DLY       ( 1'b1         ),
      .A_ADDR      ( addr_i[9:0]  ),
      .A_BM        ( bm8          ),
      .A_MEN       ( req_i        ),
      .A_WEN       ( write_i      ),
      .A_REN       ( ~write_i     ),
      .A_DIN       ( wdata8       ),
      .A_DOUT      ( rdata8       ),
      .A_BIST_CLK  ( 1'b0         ),
      .A_BIST_ADDR ( 10'd0        ),
      .A_BIST_DIN  ( 8'd0         ),
      .A_BIST_BM   ( 8'd0         ),
      .A_BIST_MEN  ( 1'b0         ),
      .A_BIST_WEN  ( 1'b0         ),
      .A_BIST_REN  ( 1'b0         ),
      .A_BIST_EN   ( 1'b0         )
    );

  // Width 144 and Depth 131072 for rram_macro data array
  end else if (Depth == 131072 && Width == 144) begin : gen_131072x144
    // No byte mask on this macro: callers must write full 144-bit words.
    logic unused_wmask;
    assign unused_wmask = ^wmask_i;

    IHPSG13_SYNTHETIC_RRAM_1P_131072x144 i_cut (
      .A_CLK  ( clk_i        ),
      .A_DLY  ( 1'b1         ),
      .A_ADDR ( addr_i[16:0] ),
      .A_MEN  ( req_i        ),
      .A_WEN  ( write_i      ),
      .A_REN  ( ~write_i     ),
      .A_DIN  ( wdata_i      ),
      .A_DOUT ( rdata_o      )
    );

  // Width 144 and Depth 256 for rram_macro info array
  end else if (Depth == 256 && Width == 144) begin : gen_256x144
    // No byte mask on this macro: callers must write full 144-bit words.
    logic unused_wmask;
    assign unused_wmask = ^wmask_i;

    IHPSG13_SYNTHETIC_RRAM_1P_256x144 i_cut (
      .A_CLK  ( clk_i       ),
      .A_DLY  ( 1'b1        ),
      .A_ADDR ( addr_i[7:0] ),
      .A_MEN  ( req_i       ),
      .A_WEN  ( write_i     ),
      .A_REN  ( ~write_i    ),
      .A_DIN  ( wdata_i     ),
      .A_DOUT ( rdata_o     )
    );

  // Width 22 and Depth 8192 for the darjeeling otp_macro array (16 data + 6 ECC bits)
  end else if (Depth == 8192 && Width == 22) begin : gen_8192x22
    // No byte mask on this macro: otp_macro always writes full 22-bit words.
    logic unused_wmask;
    assign unused_wmask = ^wmask_i;

    IHPSG13_SYNTHETIC_OTP_1P_8192x22 i_cut (
      .A_CLK  ( clk_i        ),
      .A_DLY  ( 1'b1         ),
      .A_ADDR ( addr_i[12:0] ),
      .A_MEN  ( req_i        ),
      .A_WEN  ( write_i      ),
      .A_REN  ( ~write_i     ),
      .A_DIN  ( wdata_i      ),
      .A_DOUT ( rdata_o      )
    );

  // Width 32 and Depth 1024 for the I3C buffer
  end else if (Depth == 1024 && Width == 32) begin : gen_1024x32
    RM_IHPSG13_1P_1024x32_c2_bm_bist i_cut (
      .A_CLK        ( clk_i        ),
      .A_DLY        ( 1'b1         ),
      .A_ADDR       ( addr_i[9:0]  ),
      .A_BM         ( wmask_i      ),
      .A_MEN        ( req_i        ),
      .A_WEN        ( write_i      ),
      .A_REN        ( ~write_i     ),
      .A_DIN        ( wdata_i      ),
      .A_DOUT       ( rdata_o      ),
      .A_BIST_CLK   ( 1'b0         ),
      .A_BIST_ADDR  ( 10'd0        ),
      .A_BIST_DIN   ( 32'd0        ),
      .A_BIST_BM    ( 32'd0        ),
      .A_BIST_MEN   ( 1'b0         ),
      .A_BIST_WEN   ( 1'b0         ),
      .A_BIST_REN   ( 1'b0         ),
      .A_BIST_EN    ( 1'b0         )
    );

  // Width 52 and Depth 32 for the I3C Device Address Table.
  // The smallest PDK macro is 64 words deep, so the top address bit is tied low.
  end else if (Depth == 32 && Width == 52) begin : gen_32x52
    logic [63:0] wdata64, bm64, rdata64;

    assign wdata64 = {12'b0, wdata_i};
    assign bm64    = {12'b0, wmask_i};
    assign rdata_o = rdata64[51:0];

    RM_IHPSG13_1P_64x64_c2_bm_bist i_cut (
      .A_CLK        ( clk_i             ),
      .A_DLY        ( 1'b1              ),
      .A_ADDR       ( {1'b0, addr_i}    ),
      .A_BM         ( bm64              ),
      .A_MEN        ( req_i             ),
      .A_WEN        ( write_i           ),
      .A_REN        ( ~write_i          ),
      .A_DIN        ( wdata64           ),
      .A_DOUT       ( rdata64           ),
      .A_BIST_CLK   ( 1'b0              ),
      .A_BIST_ADDR  ( 6'd0              ),
      .A_BIST_DIN   ( 64'd0             ),
      .A_BIST_BM    ( 64'd0             ),
      .A_BIST_MEN   ( 1'b0              ),
      .A_BIST_WEN   ( 1'b0              ),
      .A_BIST_REN   ( 1'b0              ),
      .A_BIST_EN    ( 1'b0              )
    );

  // Width 72 and Depth 32 for the I3C Device Characteristics Table.
  // The smallest PDK macro is 64 words deep, so the top address bits are tied low.
  // The 64x16 macro has no write mask, so the upper byte uses the masked 256x8 macro instead.
  end else if (Depth == 32 && Width == 72) begin : gen_32x72
    logic [63:0] wdata64, bm64, rdata64;
    logic [7:0]  wdata8,  bm8,  rdata8;

    assign wdata64 = wdata_i[63:0];
    assign bm64    = wmask_i[63:0];
    assign wdata8  = wdata_i[71:64];
    assign bm8     = wmask_i[71:64];
    assign rdata_o = {rdata8, rdata64};

    RM_IHPSG13_1P_64x64_c2_bm_bist i_cut_lo (
      .A_CLK        ( clk_i             ),
      .A_DLY        ( 1'b1              ),
      .A_ADDR       ( {1'b0, addr_i}    ),
      .A_BM         ( bm64              ),
      .A_MEN        ( req_i             ),
      .A_WEN        ( write_i           ),
      .A_REN        ( ~write_i          ),
      .A_DIN        ( wdata64           ),
      .A_DOUT       ( rdata64           ),
      .A_BIST_CLK   ( 1'b0              ),
      .A_BIST_ADDR  ( 6'd0              ),
      .A_BIST_DIN   ( 64'd0             ),
      .A_BIST_BM    ( 64'd0             ),
      .A_BIST_MEN   ( 1'b0              ),
      .A_BIST_WEN   ( 1'b0              ),
      .A_BIST_REN   ( 1'b0              ),
      .A_BIST_EN    ( 1'b0              )
    );

    RM_IHPSG13_1P_256x8_c3_bm_bist i_cut_hi (
      .A_CLK        ( clk_i             ),
      .A_DLY        ( 1'b1              ),
      .A_ADDR       ( {3'b0, addr_i}    ),
      .A_BM         ( bm8               ),
      .A_MEN        ( req_i             ),
      .A_WEN        ( write_i           ),
      .A_REN        ( ~write_i          ),
      .A_DIN        ( wdata8            ),
      .A_DOUT       ( rdata8            ),
      .A_BIST_CLK   ( 1'b0              ),
      .A_BIST_ADDR  ( 8'd0              ),
      .A_BIST_DIN   ( 8'd0              ),
      .A_BIST_BM    ( 8'd0              ),
      .A_BIST_MEN   ( 1'b0              ),
      .A_BIST_WEN   ( 1'b0              ),
      .A_BIST_REN   ( 1'b0              ),
      .A_BIST_EN    ( 1'b0              )
    );

  end else begin : gen_blackbox

  assign rdata_o = '0;

  `ifndef SYNTHESIS
    initial $fatal("No prim_ram_1p macro for %m: Depth %0d, Width %0d", Depth, Width);
  `endif

  `ifdef SYNTHESIS
    (* dont_touch = "true" *)
    prim_ram_1p_blackbox #(
      .Width          ( Width          ),
      .Depth          ( Depth          ),
      .DataBitsPerMask( DataBitsPerMask)
    ) i_sram_blackbox ();
  `endif

  end

endmodule
