// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Keccak state read

`include "prim_assert.sv"

module kmac_staterd
  import kmac_pkg::*;
#(
  // TL-UL Address Width. Should be bigger than
  // $clog2(kmac_pkg::StateW) * Share
  parameter int AddrW = 9,

  // EnMasking: Enable masking security hardening inside keccak_round
  // If it is enabled, the result digest will be two set of 1600bit.
  parameter  bit EnMasking = 1'b0,
  localparam int Share = (EnMasking) ? 2 : 1  // derived parameter
) (
  input clk_i,
  input rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // State in
  input [sha3_pkg::StateW-1:0] state_i [Share],

  // Config
  input endian_swap_i
);

  localparam int StateAddrW = $clog2(sha3_pkg::StateW/32);
  localparam int SelAddrW   = AddrW-2-StateAddrW;

  /////////////
  // Signals //
  /////////////

  // TL-UL Adapter signals
  logic             tlram_req;
  logic             tlram_gnt;
  logic             tlram_we;
  logic [AddrW-3:0] tlram_addr;   // Word base
  logic [31:0]      unused_tlram_wdata;
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
    .ByteAccess  (1),
    .ErrOnWrite  (1),
    .ErrOnRead   (0)
  ) u_tlul_adapter (
    .clk_i,
    .rst_ni,

    .tl_i,
    .tl_o,
    .en_ifetch_i (prim_mubi_pkg::MuBi4False),
    .req_o       (tlram_req),
    .req_type_o  (),
    .gnt_i       (tlram_gnt),
    .we_o        (tlram_we ),
    .addr_o      (tlram_addr),
    .wdata_o     (unused_tlram_wdata),
    .wmask_o     (unused_tlram_wmask),
    .intg_error_o(),
    .rdata_i     (tlram_rdata),
    .rvalid_i    (tlram_rvalid),
    .rerror_i    (tlram_rerror)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      tlram_rdata <= '0;
    end else if (tlram_req & ~tlram_we) begin
      tlram_rdata <= conv_endian32(tlram_rdata_endian, endian_swap_i);
    end
  end

  // Always grant
  assign tlram_gnt = tlram_req & ~tlram_we;

  // always no error on reading
  assign tlram_rerror = '0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) tlram_rvalid <= 1'b0;
    else         tlram_rvalid <= tlram_req & !tlram_we;
  end

  logic [31:0] muxed_state [Share];


  for (genvar i = 0 ; i < Share ; i++) begin : gen_slicer
    prim_slicer #(
      .InW (sha3_pkg::StateW),
      .OutW (32),
      .IndexW (StateAddrW)
    ) u_state_slice (
      .sel_i (tlram_addr[StateAddrW-1:0]),
      .data_i (state_i[i]),
      .data_o (muxed_state[i])
    );
  end : gen_slicer

  logic [SelAddrW-1:0] addr_sel;
  assign addr_sel = tlram_addr[StateAddrW+:SelAddrW];

  assign tlram_rdata_endian = int'(addr_sel) < Share ? muxed_state[addr_sel] : 0;

endmodule
