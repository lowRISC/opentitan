// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Synchronous single-port SRAM model

`include "prim_assert.sv"

module prim_generic_ram_1p import prim_ram_1p_pkg::*; #(
  parameter  int Width           = 32, // bit
  parameter  int Depth           = 128,
  parameter  int DataBitsPerMask = 1, // Number of data bits per bit of write mask
  parameter      MemInitFile     = "", // VMEM file to initialize the memory with

  localparam int Aw              = $clog2(Depth)  // derived parameter
) (
  input  logic             clk_i,

  input  logic             req_i,
  input  logic             write_i,
  input  logic [Aw-1:0]    addr_i,
  input  logic [Width-1:0] wdata_i,
  input  logic [Width-1:0] wmask_i,
  output logic [Width-1:0] rdata_o, // Read data. Data is returned one cycle after req_i is high.
  input ram_1p_cfg_t       cfg_i
);

// For certain synthesis experiments we compile the design with generic models to get an unmapped
// netlist (GTECH). In these synthesis experiments, we typically black-box the memory models since
// these are going to be simulated using plain RTL models in netlist simulations. This can be done
// by analyzing and elaborating the design, and then removing the memory submodules before writing
// out the verilog netlist. However, memory arrays can take a long time to elaborate, and in case
// of dual port rams they can even trigger elab errors due to multiple processes writing to the
// same memory variable concurrently. To this end, we exclude the entire logic in this module in
// these runs with the following macro.
`ifndef SYNTHESIS_MEMORY_BLACK_BOXING

  // Width must be fully divisible by DataBitsPerMask
  `ASSERT_INIT(DataBitsPerMaskCheck_A, (Width % DataBitsPerMask) == 0)

  logic unused_cfg;
  assign unused_cfg = ^cfg_i;

  // Width of internal write mask. Note wmask_i input into the module is always assumed
  // to be the full bit mask
  localparam int MaskWidth = Width / DataBitsPerMask;

  logic [Width-1:0]     mem [Depth];
  logic [MaskWidth-1:0] wmask;

  for (genvar k = 0; k < MaskWidth; k++) begin : gen_wmask
    assign wmask[k] = &wmask_i[k*DataBitsPerMask +: DataBitsPerMask];

    // Ensure that all mask bits within a group have the same value for a write
    `ASSERT(MaskCheck_A, req_i && write_i |->
        wmask_i[k*DataBitsPerMask +: DataBitsPerMask] inside {{DataBitsPerMask{1'b1}}, '0},
        clk_i, '0)
  end

  // using always instead of always_ff to avoid 'ICPD  - illegal combination of drivers' error
  // thrown when using $readmemh system task to backdoor load an image
  always @(posedge clk_i) begin
    if (req_i) begin
      if (write_i) begin
        for (int i=0; i < MaskWidth; i = i + 1) begin
          if (wmask[i]) begin
            mem[addr_i][i*DataBitsPerMask +: DataBitsPerMask] <=
              wdata_i[i*DataBitsPerMask +: DataBitsPerMask];
          end
        end
      end else begin
        rdata_o <= mem[addr_i];
      end
    end
  end

  `include "prim_util_memload.svh"
`endif
endmodule
