// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Keccak state read and write

`include "prim_assert.sv"

module kmac_staterdwr
  import kmac_pkg::*;
#(
  // TL-UL Address Width. Should be bigger than
  // $clog2(StateW) * Share
  parameter int AddrW = 9,

  // Keccak state width and the width of a single state write from the bus.
  parameter int unsigned StateW       = 1600,
  parameter int unsigned StateWrWidth = 32,

  // EnMasking: Enable masking security hardening inside keccak_round
  // If it is enabled, the result digest will be two set of 1600bit.
  parameter  bit EnMasking = 1'b0,
  // derived parameters
  localparam int          Share          = (EnMasking) ? 2 : 1,
  localparam int unsigned StateWrEntries = StateW / StateWrWidth,
  localparam int unsigned StateWrAddrW   = $clog2(StateWrEntries)
) (
  input clk_i,
  input rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // State in
  input [StateW-1:0] state_i [Share],

  // State out, used to restore the state
  input                           state_write_en_i,
  output logic [Share-1:0]        state_we_o,
  output logic [StateWrAddrW-1:0] state_waddr_o,
  output logic [StateWrWidth-1:0] state_wdata_o,

  // Config
  input endian_swap_i
);

  localparam int SelAddrW = AddrW-2-StateWrAddrW;

  /////////////
  // Signals //
  /////////////

  // TL-UL Adapter signals
  logic             tlram_req;
  logic             tlram_gnt;
  logic             tlram_we;
  logic [AddrW-3:0] tlram_addr;   // Word base
  logic [31:0]      tlram_wdata;
  logic [31:0]      unused_tlram_wmask;
  logic [31:0]      tlram_rdata;
  logic             tlram_rvalid;
  logic [1:0]       tlram_rerror;
  logic [31:0]      tlram_rdata_endian;

  // TL Adapter
  tlul_adapter_sram #(
    .SramAw (AddrW-2),
    .SramDw (32),
    .Outstanding (1),
    .ByteAccess  (0),
    .ErrOnWrite  (0),
    .ErrOnRead   (0)
  ) u_tlul_adapter (
    .clk_i,
    .rst_ni,

    .tl_i,
    .tl_o,
    .en_ifetch_i                (prim_mubi_pkg::MuBi4False),
    .req_o                      (tlram_req),
    .req_type_o                 (),
    .gnt_i                      (tlram_gnt),
    .we_o                       (tlram_we ),
    .addr_o                     (tlram_addr),
    .wdata_o                    (tlram_wdata),
    .wmask_o                    (unused_tlram_wmask),
    .intg_error_o               (),
    .user_rsvd_o                (),
    .rdata_i                    (tlram_rdata),
    .rvalid_i                   (tlram_rvalid),
    .rerror_i                   (tlram_rerror),
    .compound_txn_in_progress_o (),
    .readback_en_i              (prim_mubi_pkg::MuBi4False),
    .readback_error_o           (),
    .wr_collision_i             (1'b0),
    .write_pending_i            (1'b0)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      tlram_rdata <= '0;
    end else if (tlram_req & ~tlram_we) begin
      tlram_rdata <= conv_endian32(tlram_rdata_endian, endian_swap_i);
    end
  end

  // Always grant
  assign tlram_gnt = 1'b1;

  // always no error on reading
  assign tlram_rerror = '0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) tlram_rvalid <= 1'b0;
    else         tlram_rvalid <= tlram_req & !tlram_we;
  end

  logic [31:0] muxed_state [Share];


  for (genvar i = 0 ; i < Share ; i++) begin : gen_slicer
    prim_slicer #(
      .InW (StateW),
      .OutW (32),
      .IndexW (StateWrAddrW)
    ) u_state_slice (
      .sel_i (tlram_addr[StateWrAddrW-1:0]),
      .data_i (state_i[i]),
      .data_o (muxed_state[i])
    );
  end : gen_slicer

  logic [SelAddrW-1:0] addr_sel;
  assign addr_sel = tlram_addr[StateWrAddrW+:SelAddrW];

  if (EnMasking) begin : gen_state_sel_masked
    assign tlram_rdata_endian = int'(addr_sel) < Share ? muxed_state[addr_sel] : 0;
  end else begin : gen_state_sel_unmasked
    assign tlram_rdata_endian = int'(addr_sel) < Share ? muxed_state[0] : 0;
  end

  /////////////////
  // State write //
  /////////////////

  // Writes that are not allowed are acked on the bus and dropped.
  logic state_wr;
  assign state_wr = tlram_req & tlram_we & state_write_en_i;

  // Only the first StateWrEntries words of a share map to the Keccak state.
  logic state_waddr_valid;
  assign state_waddr_valid = tlram_addr[StateWrAddrW-1:0] < StateWrEntries;

  for (genvar i = 0 ; i < Share ; i++) begin : gen_state_we
    assign state_we_o[i] = state_wr & state_waddr_valid & (int'(addr_sel) == i);
  end : gen_state_we

  assign state_waddr_o = tlram_addr[StateWrAddrW-1:0];
  assign state_wdata_o = conv_endian32(tlram_wdata, endian_swap_i);

endmodule
