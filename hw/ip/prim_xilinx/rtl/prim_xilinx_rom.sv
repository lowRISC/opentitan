// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_xilinx_rom import prim_rom_pkg::*; #(
  parameter  int Width       = 32,
  parameter  int Depth       = 2048, // 8kB default
  parameter  string MemInitFile = "", // VMEM file to initialize the memory with

  localparam int Aw          = $clog2(Depth)
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             req_i,
  input  logic [Aw-1:0]    addr_i,
  output logic [Width-1:0] rdata_o,
  input rom_cfg_t          cfg_i
);

  logic unused_signals;
  assign unused_signals = ^{cfg_i, rst_ni};

  if (MemInitFile != "") begin : gen_generic

    logic [Width-1:0] mem [Depth];

    always_ff @(posedge clk_i) begin
      if (req_i) begin
        rdata_o <= mem[addr_i];
      end
    end

    `include "prim_util_memload.svh"
  end else begin : gen_xpm
    xpm_memory_sprom #(
     .ADDR_WIDTH_A(Aw),
     .AUTO_SLEEP_TIME(0),
     .CASCADE_HEIGHT(0),
     .MEMORY_OPTIMIZATION("false"),
     .MEMORY_SIZE(Width * Depth),
     .READ_DATA_WIDTH_A(Width),
     .READ_LATENCY_A(1),
     .USE_MEM_INIT_MMI(1)
    ) xpm_memory_sprom_inst (
     .clka(clk_i),
     .rsta(1'b0),
     .ena(req_i),
     .addra(addr_i),
     .douta(rdata_o),
     .dbiterra(),
     .sbiterra(),
     .injectdbiterra(1'b0),
     .injectsbiterra(1'b0),
     .regcea(1'b1),
     .sleep(1'b0)
    );
  end


  ////////////////
  // ASSERTIONS //
  ////////////////

  // Control Signals should never be X
  `ASSERT(noXOnCsI, !$isunknown(req_i), clk_i, '0)
endmodule
