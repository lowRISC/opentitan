// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"
`define DUMMYBOY

module prim_rom import prim_rom_pkg::*; #(
  parameter  int Width       = 32,
  parameter  int Depth       = 2048, // 8kB default
  parameter      MemInitFile = "", // VMEM file to initialize the memory with
  localparam int Aw          =  $clog2(Depth)
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             fake_i,
  input  logic             req_i,
  input  logic [Aw-1:0]    addr_i,
  output logic [Width-1:0] rdata_o,
  input rom_cfg_t          cfg_i
);
   
`ifdef TARGET_SYNTHESIS
 `ifndef FAKE
/*
  logic [Width-1:0] rdata_secure, rdata_debug;
  assign rdata_o = fake_i ? rdata_debug : rdata_secure;

  xilinx_rom_fake_bank_8192x40 fake_rom_mem_i (
                                              .clk  (clk_i),
                                              .a (addr_i),
                                              .spo (rdata_debug)
                                              );
  */
  xilinx_rom_bank_8192x40 rom_mem_i (
                                    .clk  (clk_i),
                                    .a (addr_i),
                                    .spo (rdata_o)
                                    );
     
  logic  unused; 
  assign unused = ^req_i & ^cfg_i & rst_ni;
 `else 
  
  logic unused; 
  assign rdata_o = '0;
  assign unused = ^{clk_i, addr_i, req_i, cfg_i}; 
 `endif 
  /*   tc_sram #(
     .NumWords(Depth),
     .DataWidth(Width),
     .NumPorts(32'd1),
     .MemInitFile(MemInitFile)
    // .PrintSimCfg(PrintSimCfg)
  ) rom_primitive (
     .clk_i,
     .rst_ni,
     .req_i,
     .addr_i,
     .wdata_i(1'b0),
     .rdata_o,
     .we_i(1'b0),
     .be_i('1)
  );*/
`else
  logic unused_cfg;
  assign unused_cfg = ^cfg_i;

  logic [Width-1:0] mem [Depth];

  always_ff @(posedge clk_i) begin
    rdata_o <= '0;
    if (req_i) begin
      rdata_o <= mem[addr_i];
    end
  end

  initial begin

     for(int i=0; i< Depth; i++) begin

        mem[i] = '0;
        
     end
     
  end

  `include "prim_util_memload.svh"

  ////////////////
  // ASSERTIONS //
  ////////////////

  // Control Signals should never be X
  `ASSERT(noXOnCsI, !$isunknown(req_i), clk_i, '0)

`endif

endmodule
