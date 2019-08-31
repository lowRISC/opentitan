// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Synchronous dual-port SRAM register model
//   This module is for simulation and small size SRAM.
//   Implementing ECC should be done inside wrapper not this model.

module ram_1p #(
    parameter int Width    = 32, // bit
    parameter int Depth    = 128,

    // Do not touch
    parameter int Aw = $clog2(Depth)
) (
    input                    clk_i,
    input                    rst_ni,

    input                    req_i,
    input                    write_i,
    input        [Aw-1:0]    addr_i,
    input        [Width-1:0] wdata_i,
    output logic             rvalid_o,
    output logic [Width-1:0] rdata_o
);

  logic [Width-1:0] storage [Depth];

  // Xilinx FPGA specific Dual-port RAM coding style
  // using always instead of always_ff to avoid 'ICPD  - illegal combination of drivers' error
  // thrown due to 'storage' being driven by two always processes below
  always @(posedge clk_i) begin
    if (req_i) begin
      if (write_i) begin
        storage[addr_i] <= wdata_i;
      end
      rdata_o <= storage[addr_i];
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvalid_o <= '0;
    end else begin
      rvalid_o <= req_i && ~write_i;
    end
  end

  `ifdef SRAM_INIT_FILE
    localparam MEM_FILE = `"`SRAM_INIT_FILE`";
    initial begin
      $display("Initializing SRAM from %s", MEM_FILE);
      $readmemh(MEM_FILE, storage);
    end
  `endif
endmodule

