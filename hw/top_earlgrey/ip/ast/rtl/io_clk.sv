// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: io_clk
// *Module Description: IO Clock
//############################################################################
`timescale 1ns / 10ps

module io_clk
#(
`ifndef VERILATOR
// synopsys translate_off
  parameter time IO_EN_RDLY = 5us
// synopsys translate_on
`endif
) (
  input clk_src_io_en_i,           // IO Source Clock Enable
  input clk_io_pd_ni,              // IO Clock Power-down
  input rst_io_clk_ni,             // IO Clock Logic reset
  input vcore_pok_h_i,             // VCORE POK @3.3V (for OSC)
  output logic clk_src_io_o,       // IO Source Clock
  output logic clk_src_io_val_o    // IO Source Clock Valid
);

logic clk, io_clk_en, io_clk_val, rst_n;

assign rst_n = rst_io_clk_ni;

assign io_clk_en = clk_src_io_en_i && clk_io_pd_ni;

// Behavioral Model

// Clock Oscilator
io_osc #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .IO_EN_RDLY ( IO_EN_RDLY )
// synopsys translate_on
`endif
) u_io_osc (
/*I*/ .vcore_pok_h_i ( vcore_pok_h_i ),
/*I*/ .io_en_i ( io_clk_en ),
/*O*/ .io_clk_o ( clk )
);


// Clock & Valid
assign clk_src_io_o = clk;

wire rst_val_n = rst_n && io_clk_en;

// 2-stage deassertion
always_ff @( posedge clk, negedge rst_val_n ) begin
  if ( !rst_val_n )  begin
    io_clk_val       <= 1'b0;
    clk_src_io_val_o <= 1'b0;
  end else begin
    io_clk_val       <= 1'b1;
    clk_src_io_val_o <= io_clk_val;
  end
end


endmodule  // of io_clk
