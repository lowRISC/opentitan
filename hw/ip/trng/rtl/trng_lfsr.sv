// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: TRNG lfsr module
//

module trng_lfsr
  (
   // INPUTS               
   input logic        clk_i,
   input logic        rst_ni,
   input logic [31:0] seed_value_i,
   input logic        load_seed_i,
   input logic        incr_lfsr_i,
   // OUTPUTS
   output logic [31:0] lfsr_value_o
   );

  //   
  // define the state machine variable
  logic [32:1] lfsr_q, lfsr_d; // note: different bit numbering here
  
  // connect feedback path for all flops  
  always @(posedge clk_i or negedge rst_ni) begin
    if(rst_ni == 1'b0) begin 
      lfsr_q        <= 32'h00000000;
    end else begin
      lfsr_q        <= lfsr_d;
    end
  end
  
  // make an lfsr for psuedo random effects
  // implement primary polynomial taps 32,30,26,25
  // reference: table of linear feedback shift registers, Roy Ward, Tim Molteno, October 26, 2007
  assign lfsr_d = load_seed_i ? seed_value_i :
                  !incr_lfsr_i ? lfsr_q :
                  //     q32      q31                    q30     q29-q27                    q26                    q25      q24-q1
                  {lfsr_q[1],lfsr_q[32],(lfsr_q[1] ^ lfsr_q[31]),lfsr_q[30:28],(lfsr_q[1] ^ lfsr_q[27]),(lfsr_q[1] ^ lfsr_q[26]),lfsr_q[25:2]};
  
  assign lfsr_value_o = lfsr_q;

endmodule
