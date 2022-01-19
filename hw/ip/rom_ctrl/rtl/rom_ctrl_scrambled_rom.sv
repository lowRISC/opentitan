// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

//
// A scrambled ROM. This is scrambled with a fixed key, passed in as a parameter (this parameter
// will be a compile-time random constant).
//
// This code follows the structure of prim_ram_1p_scr.sv (although it's much simplified because the
// key is fixed and we don't support writes). For more information about what is going on, see that
// file. Using the parameter names in prim_ram_1p_scr, we have NumPrinceRoundsHalf = 2 (so
// approximately 5 effective rounds), NumDiffRounds = 2 and NumAddrScrRounds = 2 (enabling address
// scrambling with 2 rounds).
//
// There are two input address ports (rom_addr_i and prince_addr_i). These are expected to be
// connected to signals that are logically the same. The first is used as an input to the physical
// ROM index. The second is used when calculating the address-tweakable keystream. The trick is that
// you can mitigate fault-injection attacks that corrupt the address by splitting it somewhere
// "upstream". If a fault-injection only corrupts one of the two addresses, the result will be
// garbage.

module rom_ctrl_scrambled_rom
  import prim_rom_pkg::rom_cfg_t;
#(
  // The initial contents of the ROM. This is used for synthesis. For simulation, this is not used;
  // instead, the simulator loads the contents of ROM over DPI.
  //
  // In either case, the input file should be scrambled. That is, it should contain the bits that
  // will appear in the physical ROM.
  parameter MemInitFile = "",

  // The width of ROM words in bits
  parameter int Width = 40,

  // The number of words in the ROM
  parameter int Depth = 16,

  // The nonce for data and address scrambling
  parameter bit [63:0] ScrNonce = '0,

  // The (fixed) key for the PRINCE cipher
  parameter bit [127:0] ScrKey = '0,

  localparam int Aw = $clog2(Depth)
) (
  input logic              clk_i,
  input logic              rst_ni,

  input  logic             req_i,
  input  logic [Aw-1:0]    rom_addr_i,
  input  logic [Aw-1:0]    prince_addr_i,
  output logic             rvalid_o,
  output logic [Width-1:0] scr_rdata_o,
  output logic [Width-1:0] clr_rdata_o,

  input rom_cfg_t          cfg_i
);

  /////////////////////////////////////
  // Anchor incoming seeds and constants
  /////////////////////////////////////
  localparam int TotalAnchorWidth = $bits(ScrNonce) +
                                    $bits(ScrKey);

  logic [63:0] scr_nonce;
  logic [127:0] scr_key;

  prim_sec_anchor_buf #(
    .Width(TotalAnchorWidth)
  ) u_seed_anchor (
    .in_i({ScrNonce,
           ScrKey}),
    .out_o({scr_nonce,
            scr_key})
  );

  logic [63-Aw:0] data_scr_nonce;
  logic [Aw-1:0] addr_scr_nonce;
  assign data_scr_nonce = scr_nonce[63-Aw:0];
  assign addr_scr_nonce = scr_nonce[63-:Aw];

  // Parameter Checks ==========================================================

  // The depth needs to be a power of 2 to use address scrambling
  `ASSERT_INIT(DepthPow2Check_A, (Depth & (Depth - 1)) == 0)
  // We only support a width up to 64
  `ASSERT_INIT(MaxWidthCheck_A, Width <= 64)

  // Address scrambling ========================================================

  logic [Aw-1:0] addr_scr;
  prim_subst_perm #(
    .DataWidth (Aw),
    .NumRounds (2),
    .Decrypt   (0)
  ) u_sp_addr (
    .data_i (rom_addr_i),
    .key_i  (addr_scr_nonce),
    .data_o (addr_scr)
  );

  // Keystream generation ======================================================

  logic [63:0] keystream;

  prim_prince #(
    .DataWidth      (64),
    .KeyWidth       (128),
    .NumRoundsHalf  (2),
    .HalfwayDataReg (1'b1),
    .HalfwayKeyReg  (1'b1)
  ) u_prince (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .valid_i (req_i),
    .data_i  ({data_scr_nonce, prince_addr_i}),
    .key_i   (scr_key),
    .dec_i   (1'b0),
    .data_o  (keystream),
    .valid_o ()
  );

  if (Width < 64) begin : gen_unread_keystream
    // Ignore top bits of keystream: we just use the bottom Width bits.
    logic unused_top_keystream;
    assign unused_top_keystream = ^keystream[63:Width];
  end

  // The physical ROM ==========================================================

  logic [Width-1:0] rdata_scr;

  prim_rom_adv #(
    .Width       (Width),
    .Depth       (Depth),
    .MemInitFile (MemInitFile)
  ) u_rom (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .req_i    (req_i),
    .addr_i   (addr_scr),
    .rvalid_o (rvalid_o),
    .rdata_o  (rdata_scr),
    .cfg_i    (cfg_i)
  );

  assign scr_rdata_o = rdata_scr;

  // Data scrambling ===========================================================

  logic [Width-1:0] rdata_xor;

  prim_subst_perm #(
    .DataWidth (Width),
    .NumRounds (2),
    .Decrypt   (1)
  ) u_sp_data (
    .data_i (rdata_scr),
    .key_i  ('0),
    .data_o (rdata_xor)
  );

  // XOR rdata with keystream ==================================================

  assign clr_rdata_o = rdata_xor ^ keystream[Width-1:0];

endmodule
