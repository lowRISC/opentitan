// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: io_clk
// *Module Description: IO Clock
//############################################################################
`timescale 1ns / 10ps

module io_clk #(
`ifndef VERILATOR
// synopsys translate_off
  parameter time IO_EN_RDLY = 5us
// synopsys translate_on
`endif
) (
  input vcmain_pok_i,              // VCMAIN POK @1.1V
  input clk_src_io_en_i,           // IO Source Clock Enable
  output logic clk_src_io_o,       // IO Source Clock
  output logic clk_src_io_val_o    // IO Source Clock Valid
);

logic clk, io_clk_val, rst_n;

// Behavioral Model
assign rst_n = vcmain_pok_i;

// Clock Oscilator
io_osc #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .IO_EN_RDLY ( IO_EN_RDLY )
// synopsys translate_on
`endif
) i_io_osc (
/*I*/ .vcmain_pok_i ( vcmain_pok_i ),
/*I*/ .io_en_i ( clk_src_io_en_i ),
/*O*/ .io_clk_o ( clk )
);


// Clock & Valid
assign clk_src_io_o = clk;

wire rst_val_n = rst_n && clk_src_io_en_i;

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
