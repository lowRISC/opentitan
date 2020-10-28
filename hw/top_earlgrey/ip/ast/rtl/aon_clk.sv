// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: aon_clk
// *Module Description: Always ON Clock
//############################################################################
`timescale 1ns / 10ps

module aon_clk #(
`ifndef VERILATOR
// synopsys translate_off
  parameter time AON_EN_RDLY = 5us
// synopsys translate_on
`endif
) (
  input vcaon_pok_i,              // 1.1v VCAON POK
  output logic clk_src_aon_o,     // AON Source Clock
  output logic clk_src_aon_val_o  // AON Source Clock Valid
);

logic clk, aon_clk_en, aon_clk_val, aon_en, rst_n;
assign aon_en = 1'b1;  // AON Clock is always enabled!

// Behavioral Model
assign rst_n = vcaon_pok_i;

aon_osc #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .AON_EN_RDLY ( AON_EN_RDLY )
// synopsys translate_on
`endif
) i_aon_osc (
/*I*/ .vcaon_pok_i ( vcaon_pok_i ),
/*I*/ .aon_en_i ( aon_en ),
/*O*/ .aon_clk_o ( clk )
);


// Clock & Valid
assign clk_src_aon_o = clk;

wire rst_val_n = rst_n;

// 2-stage deassertion
always_ff @( posedge clk, negedge rst_val_n ) begin
  if ( !rst_val_n )  begin
    aon_clk_val       <= 1'b0;
    clk_src_aon_val_o <= 1'b0;
  end else begin
    aon_clk_val       <= 1'b1;
    clk_src_aon_val_o <= aon_clk_val;
  end
end


endmodule  // of aon_clk
