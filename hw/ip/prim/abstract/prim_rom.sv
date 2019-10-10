// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_rom #(
  parameter  int Width     = 32,
  parameter  int Depth     = 2048, // 8kB default
  parameter      Impl      = "generic",
  parameter  int Aw        = $clog2(Depth)
) (
  input                        clk_i,
  input                        rst_ni,
  input        [Aw-1:0]        addr_i,
  input                        cs_i,
  output logic [Width-1:0]     dout_o,
  output logic                 dvalid_o
);

  if (Impl == "generic") begin: gen_mem_generic
    prim_generic_rom #(
      .Width(Width),
      .Depth(Depth),
      .Init(1)
    ) u_impl_generic (
      .clk_i,
      .rst_ni,
      .addr_i,
      .cs_i,
      .dout_o,
      .dvalid_o
    );
  end else if (Impl == "xilinx") begin: gen_rom_xilinx
    // For fpga synthesis, a ram is still used to ensure the tools can properly infer
    // BRAM
    prim_generic_ram_1p #(
      .Width(Width),
      .Depth(Depth),
      .DataBitsPerMask(1),
      .Init(1)
    ) u_impl_xilinx (
      .clk_i,
      .rst_ni,
      .req_i(cs_i),
      .write_i(1'b0),
      .addr_i,
      .wdata_i(Width'(0)),
      .wmask_i(1'b0),
      .rvalid_o(dvalid_o),
      .rdata_o(dout_o)
    );
  end else begin : gen_rom_unsupported_impl
    // TODO: Find code that works across tools and causes a compile failure
  end

endmodule
