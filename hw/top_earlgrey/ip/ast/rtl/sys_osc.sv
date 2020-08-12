// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// 
// *Name: sys_osc
// *Module Description: System Clock Oscilator
//
//############################################################################
`timescale 1ns/1ps

module sys_osc #(
// synopsys translate_off
   parameter time SYS_EN_RDLY = 10us,
   parameter time SYS_EN_FDLY = 100ns,
   parameter time SYS_JEN_RDLY = 80ns,
   parameter time SYS_JEN_FDLY = 80ns
// synopsys translate_on
) (
   input sys_en_i,              // System Source Clock Enable
   input sys_jen_i,             // System Source Clock Jitter Enable
   output logic sys_clk_o,      // System Clock Output
   output logic sys_clk_en_o    // System Clock Enable Output
);

// synopsys translate_off
localparam real SYS_CLK_PERIOD = 10000; // 10000ps (100Mhz)

logic init_start, clk;
shortreal jitter;

initial begin
   clk  = 1'b0;
   $display("\nSYS Clock Period: %0dps", SYS_CLK_PERIOD);
   init_start = 1'b1; #1;
   init_start = 1'b0;
end

wire #(SYS_JEN_RDLY, SYS_JEN_FDLY) sys_jen = sys_jen_i; 

always begin
   // 0-2000ps is upto +20% Jitter
   jitter = sys_jen ? $urandom_range(2000, 0) : 0; 
   #((SYS_CLK_PERIOD+jitter)/2000) clk = ~clk;
end

assign sys_clk_o = clk;

always_ff @( init_start, posedge sys_en_i, negedge sys_en_i ) begin
    if ( init_start )
       sys_clk_en_o <= 1'b0;
    else if ( !init_start && sys_en_i )
       sys_clk_en_o <= #(SYS_EN_RDLY) sys_en_i;
    else if ( !init_start && !sys_en_i )                  
       sys_clk_en_o <= #(SYS_EN_FDLY) sys_en_i;
end
// synopsys translate_on


endmodule  // of sys_osc
