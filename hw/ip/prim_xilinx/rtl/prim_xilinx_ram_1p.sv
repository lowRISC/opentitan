// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Synchronous single-port SRAM model

`include "prim_assert.sv"

module prim_xilinx_ram_1p import prim_ram_1p_pkg::*; #(
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
  input ram_1p_cfg_t       cfg_i,
  output ram_1p_cfg_rsp_t  cfg_rsp_o
);

  localparam int PrimMaxWidth = prim_xilinx_pkg::get_ram_max_width(Width, Depth);

  if (PrimMaxWidth <= 0) begin : gen_generic
    prim_generic_ram_1p #(
      .Width(Width),
      .Depth(Depth),
      .DataBitsPerMask(DataBitsPerMask),
      .MemInitFile(MemInitFile)
    ) u_ram_1p (
      .*
    );
  end else begin : gen_xpm
    logic wr_en;
    assign wr_en = write_i & wmask_i[0];

    logic unused_signals;
    assign unused_signals = ^{rst_ni, cfg_i};
    assign cfg_rsp_o.done = 1'b0;

    for (genvar k = 0; k < Width; k = k + PrimMaxWidth) begin : gen_split
      localparam int PrimWidth = ((Width - k) > PrimMaxWidth) ? PrimMaxWidth : Width - k;
      localparam string PrimMemoryInitFile = (MemInitFile != "") ? MemInitFile : "none";

      xpm_memory_spram #(
        .ADDR_WIDTH_A(Aw),
        .BYTE_WRITE_WIDTH_A(PrimWidth), // Masks are not supported
        .MEMORY_INIT_FILE(PrimMemoryInitFile),
        .MEMORY_SIZE(Depth * PrimWidth),
        .READ_DATA_WIDTH_A(PrimWidth),
        .READ_LATENCY_A(1),
        .USE_MEM_INIT_MMI(1),
        .WRITE_DATA_WIDTH_A(PrimWidth)
      ) u_ram_1p (
        .clka(clk_i),
        .addra(addr_i),
        .dbiterra(),
        .dina(wdata_i[k +: PrimWidth]),
        .douta(rdata_o[k +: PrimWidth]),
        .ena(req_i),
        .injectdbiterra(1'b0),
        .injectsbiterra(1'b0),
        .regcea(1'b1),
        .rsta(1'b0),
        .sbiterra(),
        .sleep(1'b0),
        .wea(wr_en)
      );
    end
  end

endmodule
