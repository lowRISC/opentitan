// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Intercepts an outbound TL interface to instantiate an SRAM used for simulation.
module sim_sram #(
  parameter bit InstantiateSram = 1'b0, // 0: leave it as an empty sink, 1: instantiate the SRAM.
  parameter int AddrWidth       = 32,   // Should default to system address width.
  parameter int Width           = 32,   // Should default to system data width.
  parameter int Depth           = 8,    // 8 locations - can be higher if sim demands it.
  parameter bit ErrOnRead       = 1'b1  // CPU only sinks info.
) (
  input logic clk_i,
  input logic rst_ni,

  // Incoming TL access.
  input  tlul_pkg::tl_h2d_t tl_in_i,
  output tlul_pkg::tl_d2h_t tl_in_o,

  // Outgoing TL access.
  output tlul_pkg::tl_h2d_t tl_out_o,
  input  tlul_pkg::tl_d2h_t tl_out_i
);

`ifdef SYNTHESIS

  // Induce a compilation error by instantiating a non-existent module. This file should not be
  // compiled for synthesis.
  illegal_preprocessor_branch_taken u_illegal_preprocessor_branch_taken();

`else

  `include "prim_assert.sv"
  `ASSERT_INIT(WidthAlignment_A, Width[2:0] == 0)

  localparam int WidthBytes = Width >> 3;

  // Socket signals.
  tlul_pkg::tl_h2d_t tl_socket_h2d[2];
  tlul_pkg::tl_d2h_t tl_socket_d2h[2];
  logic dev_select;

  // Separate interface to set the SRAM start address (done by the testbench) & monitor the SRAM
  // access.
  sim_sram_if #(
    .AddrWidth(AddrWidth)
  ) u_sim_sram_if (
    .clk_i,
    .rst_ni,
    .tl_h2d(tl_socket_h2d[1]),
    .tl_d2h(tl_socket_d2h[1])
  );

  // Split the incoming access into two.
  tlul_socket_1n #(
    .N        (2),
    .HReqPass (1'b1),
    .HRspPass (1'b1),
    .DReqPass ({2{1'b1}}),
    .DRspPass ({2{1'b1}}),
    .HReqDepth(4'h0),
    .HRspDepth(4'h0),
    .DReqDepth({2{4'h0}}),
    .DRspDepth({2{4'h0}})
  ) u_socket (
    .clk_i,
    .rst_ni,
    .tl_h_i      (tl_in_i),
    .tl_h_o      (tl_in_o),
    .tl_d_o      (tl_socket_h2d),
    .tl_d_i      (tl_socket_d2h),
    .dev_select_i({1'b0, dev_select})
  );

  // Logic to select SRAM address range.
  assign dev_select = (tl_in_i.a_address >= u_sim_sram_if.start_addr &&
                       tl_in_i.a_address < (u_sim_sram_if.start_addr + (Depth * WidthBytes)));

  // Wire output 0 of the socket to outbound TL interface.
  assign tl_out_o = tl_socket_h2d[0];
  assign tl_socket_d2h[0] = tl_out_i;

  if (InstantiateSram) begin : gen_sram_inst

    localparam int SramAddrWidth = $clog2(Depth);

    logic                     sram_req;
    logic                     sram_we;
    logic [SramAddrWidth-1:0] sram_addr;
    logic [        Width-1:0] sram_wdata;
    logic [        Width-1:0] sram_wmask;
    logic [        Width-1:0] sram_rdata;
    logic                     sram_rvalid;

    tlul_adapter_sram #(
      .SramAw     (SramAddrWidth),
      .SramDw     (Width),
      .ErrOnRead  (ErrOnRead),
      .Outstanding(2),
      .EnableRspIntgGen(1),
      .EnableDataIntgGen(1)
    ) u_tl_adapter_sim_sram (
      .clk_i,
      .rst_ni,
      .tl_i(tl_socket_h2d[1]),
      .tl_o(tl_socket_d2h[1]),

      .req_o   (sram_req),
      .gnt_i   (1'b1),
      .we_o    (sram_we),
      .addr_o  (sram_addr),
      .wdata_o (sram_wdata),
      .wmask_o (sram_wmask),
      .rdata_i (sram_rdata),
      .rvalid_i(sram_rvalid),
      .rerror_i(2'b00)
    );

    prim_ram_1p #(
      .Width          (Width),
      .Depth          (Depth),
      .DataBitsPerMask(WidthBytes)
    ) u_sram (
      .clk_i,
      .req_i  (sram_req),
      .write_i(sram_we),
      .addr_i (sram_addr),
      .wdata_i(sram_wdata),
      .wmask_i(sram_wmask),
      .rdata_o(sram_rdata)
    );

    // Valid data from the SRAM appears 1 cycle after the sram_req.
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        sram_rvalid <= 1'b0;
      end else begin
        sram_rvalid <= sram_req & ~sram_we;
      end
    end

  end : gen_sram_inst
  else begin : gen_no_sram

    tlul_sink u_tlul_sink (
      .clk_i,
      .rst_ni,
      .tl_i(tl_socket_h2d[1]),
      .tl_o(tl_socket_d2h[1])
    );

  end : gen_no_sram

`endif

endmodule
