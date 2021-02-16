// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description RBOX combo trigger  module

module rbox_combotrg (
  input                cfg_in0_sel,
  input                cfg_in1_sel,
  input                cfg_in2_sel,
  input                cfg_in3_sel,
  input                cfg_in4_sel,
  input                in0,
  input                in1,
  input                in2,
  input                in3,
  input                in4,
  output logic         trigger_h_o,
  output logic         trigger_l_o
);

  logic [4:0] cfg_input_sel;

  assign cfg_input_sel = {cfg_in0_sel, cfg_in1_sel, cfg_in2_sel, cfg_in3_sel, cfg_in4_sel};

  always_comb begin: trigger_combo

    unique case (cfg_input_sel)
      5'b00001: begin
         trigger_h_o = (in4 == 1'b1);
         trigger_l_o = (in4 == 1'b0);
      end
      5'b00010: begin
         trigger_h_o = (in3 == 1'b1);
         trigger_l_o = (in3 == 1'b0);
      end
      5'b00011: begin
         trigger_h_o = (in3 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in3 == 1'b0) && (in4 == 1'b0);
      end
      5'b00100: begin
         trigger_h_o = (in2 == 1'b1);
         trigger_l_o = (in2 == 1'b0);
      end
      5'b00101: begin
         trigger_h_o = (in2 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in2 == 1'b0) && (in4 == 1'b0);
      end
      5'b00111: begin
         trigger_h_o = (in2 == 1'b1) && (in3 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in2 == 1'b0) && (in3 == 1'b0) && (in4 == 1'b0);
      end
      5'b01000: begin
         trigger_h_o = (in1 == 1'b1);
         trigger_l_o = (in1 == 1'b0);
      end
      5'b01001: begin
         trigger_h_o = (in1 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in1 == 1'b0) && (in4 == 1'b0);
      end
      5'b01010: begin
         trigger_h_o = (in1 == 1'b1) && (in3 == 1'b1);
         trigger_l_o = (in1 == 1'b0) && (in3 == 1'b0);
      end
      5'b01011: begin
         trigger_h_o = (in1 == 1'b1) && (in3 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in1 == 1'b0) && (in3 == 1'b0) && (in4 == 1'b0);
      end
      5'b01100: begin
         trigger_h_o = (in1 == 1'b1) && (in2 == 1'b1);
         trigger_l_o = (in1 == 1'b0) && (in2 == 1'b0);
      end
      5'b01101: begin
         trigger_h_o = (in1 == 1'b1) && (in2 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in1 == 1'b0) && (in2 == 1'b0) && (in4 == 1'b0);
      end
      5'b01110: begin
         trigger_h_o = (in1 == 1'b1) && (in2 == 1'b1) && (in3 == 1'b1);
         trigger_l_o = (in1 == 1'b0) && (in2 == 1'b0) && (in3 == 1'b0);
      end
      5'b01111: begin
         trigger_h_o = (in1 == 1'b1) && (in2 == 1'b1) && (in3 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in1 == 1'b0) && (in2 == 1'b0) && (in3 == 1'b0) && (in4 == 1'b0);
      end
      5'b10000: begin
         trigger_h_o = (in0 == 1'b1);
         trigger_l_o = (in0 == 1'b0);
      end
      5'b10001: begin
         trigger_h_o = (in0 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in4 == 1'b0);
      end
      5'b10010: begin
         trigger_h_o = (in0 == 1'b1) && (in3 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in3 == 1'b0);
      end
      5'b10011: begin
         trigger_h_o = (in0 == 1'b1) && (in3 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in3 == 1'b0) && (in4 == 1'b0);
      end
      5'b10100: begin
         trigger_h_o = (in0 == 1'b1) && (in2 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in2 == 1'b0);
      end
      5'b10101: begin
         trigger_h_o = (in0 == 1'b1) && (in2 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in2 == 1'b0) && (in4 == 1'b0);
      end
      5'b10110: begin
         trigger_h_o = (in0 == 1'b1) && (in2 == 1'b1) && (in3 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in2 == 1'b0) && (in3 == 1'b0);
      end
      5'b10111: begin
         trigger_h_o = (in0 == 1'b1) && (in2 == 1'b1) && (in3 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in2 == 1'b0) && (in3 == 1'b0) && (in4 == 1'b0);
      end
      5'b11000: begin
         trigger_h_o = (in0 == 1'b1) && (in1 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in1 == 1'b0);
      end
      5'b11001: begin
         trigger_h_o = (in0 == 1'b1) && (in1 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in1 == 1'b0) && (in4 == 1'b0);
      end
      5'b11010: begin
         trigger_h_o = (in0 == 1'b1) && (in1 == 1'b1) && (in3 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in1 == 1'b0) && (in3 == 1'b0);
      end
      5'b11011: begin
         trigger_h_o = (in0 == 1'b1) && (in1 == 1'b1) && (in3 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in1 == 1'b0) && (in3 == 1'b0) && (in4 == 1'b0);
      end
      5'b11100: begin
         trigger_h_o = (in0 == 1'b1) && (in1 == 1'b1) && (in2 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in1 == 1'b0) && (in2 == 1'b0);
      end
      5'b11101: begin
         trigger_h_o = (in0 == 1'b1) && (in1 == 1'b1) && (in2 == 1'b1) && (in4 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in1 == 1'b0) && (in2 == 1'b0) && (in4 == 1'b0);
      end
      5'b11110: begin
         trigger_h_o = (in0 == 1'b1) && (in1 == 1'b1) && (in2 == 1'b1) && (in3 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in1 == 1'b0) && (in2 == 1'b0) && (in3 == 1'b0);
      end
      5'b11111: begin
         trigger_h_o = (in0 == 1'b1) && (in1 == 1'b1) && (in2 == 1'b1) && (in3 == 1'b1) &&
           (in4 == 1'b1);
         trigger_l_o = (in0 == 1'b0) && (in1 == 1'b0) && (in2 == 1'b0) && (in3 == 1'b0) &&
           (in4 == 1'b0);
      end
      default: begin
         trigger_h_o = 1'b0;
         trigger_l_o = 1'b0;
      end
    endcase
  end

endmodule
