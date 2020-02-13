// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_generic_rom #(
  parameter  int Width     = 32,
  parameter  int Depth     = 2048, // 8kB default
  parameter  int Aw        = $clog2(Depth)
) (
  input                        clk_i,
  input                        rst_ni,
  input        [Aw-1:0]        addr_i,
  input                        cs_i,
  output logic [Width-1:0]     dout_o,
  output logic                 dvalid_o
);

  logic [Width-1:0] mem [Depth];

  always_ff @(posedge clk_i) begin
    if (cs_i) begin
      dout_o <= mem[addr_i];
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dvalid_o <= 1'b0;
    end else begin
      dvalid_o <= cs_i;
    end
  end

  ////////////////
  // ASSERTIONS //
  ////////////////

  // Control Signals should never be X
  `ASSERT(noXOnCsI, !$isunknown(cs_i), clk_i, '0)

  `ifdef VERILATOR
    // Task for loading 'mem' with SystemVerilog system task $readmemh()
    export "DPI-C" task simutil_verilator_memload;
    // Function for setting a specific 32 bit element in |mem|
    // Returns 1 (true) for success, 0 (false) for errors.
    export "DPI-C" function simutil_verilator_set_mem;

    task simutil_verilator_memload;
      input string file;
      $readmemh(file, mem);
    endtask

    // TODO: Allow 'val' to have other widths than 32 bit
    function int simutil_verilator_set_mem(input int index,
                                           input logic[31:0] val);
      if (index >= Depth) begin
        return 0;
      end

      mem[index] = val;
      return 1;
    endfunction
  `endif

  `ifdef ROM_INIT_FILE
    localparam MEM_FILE = `PRIM_STRINGIFY(`ROM_INIT_FILE);
    initial begin
      $display("Initializing ROM from %s", MEM_FILE);
      $readmemh(MEM_FILE, mem);
    end
  `endif
endmodule
