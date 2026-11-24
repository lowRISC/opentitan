// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Synchronous ROM mapped to IHP SG13CMOS5L FAKE ROM macros.
// Each supported Width/Depth combination maps to one IHPSG13_SYNTHETIC_ROM_1P_<Depth>x<Width>
// macro. The macros are synthetic (timing/area only): their contents are not modelled and
// MemInitFile is ignored, so this ROM cannot be used for functional simulation.

`include "prim_assert.sv"

module prim_rom_blackbox #(
  parameter int Width = 39,
  parameter int Depth = 49152
) ();
endmodule

module prim_rom import prim_rom_pkg::*; #(
  parameter  int Width       = 32,
  parameter  int Depth       = 2048, // 8kB default
  parameter      MemInitFile = "", // VMEM file to initialize the memory with

  localparam int Aw          = $clog2(Depth)
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             req_i,
  input  logic [Aw-1:0]    addr_i,
  output logic             rvalid_o,
  output logic [Width-1:0] rdata_o,
  input  rom_cfg_req_t     cfg_i,
  output rom_cfg_rsp_t     cfg_o
);

  logic unused_signals;
  assign unused_signals = ^{cfg_i, MemInitFile};
  assign cfg_o          = ROM_CFG_RSP_DEFAULT;

  // Data always comes in the next cycle after a request
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvalid_o <= 1'b0;
    end else begin
      rvalid_o <= req_i;
    end
  end

  // earlgrey rom_ctrl: Width=39, Depth=49152.
  if (Width == 39 && Depth == 49152) begin : gen_49152x39

    IHPSG13_SYNTHETIC_ROM_1P_49152x39 i_cut (
      .A_CLK  ( clk_i         ),
      .A_DLY  ( 1'b1          ),
      .A_ADDR ( addr_i[15:0]  ),
      .A_MEN  ( req_i         ),
      .A_REN  ( 1'b1          ),
      .A_DOUT ( rdata_o       )
    );

  // darjeeling rom_ctrl0: Width=39, Depth=8192.
  end else if (Width == 39 && Depth == 8192) begin : gen_8192x39

    IHPSG13_SYNTHETIC_ROM_1P_8192x39 i_cut (
      .A_CLK  ( clk_i         ),
      .A_DLY  ( 1'b1          ),
      .A_ADDR ( addr_i[12:0]  ),
      .A_MEN  ( req_i         ),
      .A_REN  ( 1'b1          ),
      .A_DOUT ( rdata_o       )
    );

  // darjeeling rom_ctrl1: Width=39, Depth=16384.
  end else if (Width == 39 && Depth == 16384) begin : gen_16384x39

    IHPSG13_SYNTHETIC_ROM_1P_16384x39 i_cut (
      .A_CLK  ( clk_i         ),
      .A_DLY  ( 1'b1          ),
      .A_ADDR ( addr_i[13:0]  ),
      .A_MEN  ( req_i         ),
      .A_REN  ( 1'b1          ),
      .A_DOUT ( rdata_o       )
    );

  end else begin : gen_blackbox

    assign rdata_o = '0;

    `ifndef SYNTHESIS
      initial $fatal("No prim_rom macro for %m: Width=%0d Depth=%0d - add a new branch",
          Width, Depth);
    `endif

    `ifdef SYNTHESIS
      (* dont_touch = "true" *)
      prim_rom_blackbox #(
        .Width ( Width ),
        .Depth ( Depth )
      ) i_rom_blackbox ();
    `endif

  end

endmodule
