// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Target Extension interface, for low-latency protocols that must be implemented in hardware.

module i3c_target_ext
  import i3c_targ_ext_pkg::*;
#(
  parameter int Dummy = 1'b1
) (
  input                     clk_i,
  input                     rst_ni,

  // Control signals.
  input                     enable_i,
  input                     sw_reset_i,

  // Indicator of hardware extension presence.
  output                    ext_present_o,
  // Extension info.
  input                     ext_info_qe_i,
  input              [14:0] ext_info_q_i,
  output             [14:0] ext_info_o,

  // Register interface.
  input  i3c_reg2targ_ext_t ext_reg2hw_i,
  output i3c_targ_ext2reg_t ext_hw2reg_o
);

  // Implement a simple `hwext` register to hold the information.
  //
  // Note: this simple register is exercised via a test script and should probably be replaced with
  // some information identifying the Target Extension that is present.
  logic [14:0] ext_info;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ext_info  <= 'b0;
    end else if (sw_reset_i) begin
      ext_info  <= 'b0;
    end else begin
      if (ext_info_qe_i) ext_info <= ext_info_q_i;
    end
  end
  assign ext_present_o = 1'b1;
  assign ext_info_o = ext_info;
  // No dedicated registers in this placeholder.
  assign ext_hw2reg_o = '0;

endmodule
