// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Synchronous single-port SRAM model

module prim_generic_ram_1p #(
  parameter int Width           = 32, // bit
  parameter int Depth           = 128,
  parameter int DataBitsPerMask = 1, // Number of data bits per bit of write mask
  parameter bit Init            = 0, // Initialize memory contents
  localparam int Aw             = $clog2(Depth)  // derived parameter
) (
  input clk_i,
  input rst_ni,       // Memory content reset

  input                    req_i,
  input                    write_i,
  input        [Aw-1:0]    addr_i,
  input        [Width-1:0] wdata_i,
  input        [Width-1:0] wmask_i,
  output logic             rvalid_o,
  output logic [Width-1:0] rdata_o
);

  // Width of internal write mask. Note wmask_i input into the module is always assumed
  // to be the full bit mask
  localparam int MaskWidth = Width / DataBitsPerMask;

  `ASSERT_INIT(paramCheckAw, Aw == $clog2(Depth))


  logic [Width-1:0] mem [Depth];
  logic [MaskWidth-1:0] wmask;

  always_comb begin
    for (int i=0; i < MaskWidth; i = i + 1) begin : create_wmask
      wmask[i] = &wmask_i[i*DataBitsPerMask +: DataBitsPerMask];
    end
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

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      rvalid_o <= '0;
    end else begin
      rvalid_o <= req_i & ~write_i;
    end
  end

  `ifdef VERILATOR
    export "DPI-C" task simutil_verilator_memload;

    task simutil_verilator_memload;
      input string file;
      $readmemh(file, mem);
    endtask
  `endif

  if (Init) begin : gen_init_memory
  `ifdef SRAM_INIT_FILE
      localparam MEM_FILE = `"`SRAM_INIT_FILE`";
    initial
    begin
      $display("Initializing SRAM from %s", MEM_FILE);
      $readmemh(MEM_FILE, mem);
    end
  `endif
  end
endmodule
