// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic differential receiver for USB. Note that this is meant for emulation purposes only, and
// the pull-up, calibration and pok signals are not connected in this module.

`include "prim_assert.sv"

module prim_generic_usb_diff_rx #(
  parameter int CalibW = 32
) (
  inout              input_pi,      // differential input
  inout              input_ni,      // differential input
  input              input_en_i,    // input buffer enable
  input              core_pok_h_i,  // core power indication at VCC level
  input              pullup_p_en_i, // pullup enable for P
  input              pullup_n_en_i, // pullup enable for N
  input [CalibW-1:0] calibration_i, // calibration input
  output logic       usb_diff_rx_obs_o, // observability output
  output logic       input_o        // output of differential input buffer
);

  logic [CalibW-1:0] unused_calibration;
  logic unused_core_pok;
  assign unused_calibration = calibration_i;
  assign unused_core_pok = core_pok_h_i;

  wire input_p, input_n;
  assign input_p = input_pi;
  assign input_n = input_ni;

`ifdef VERILATOR
  logic unused_pullup_p_en, unused_pullup_n_en;
  assign unused_pullup_p_en = pullup_p_en_i;
  assign unused_pullup_n_en = pullup_n_en_i;
`else
  // pullup termination
  assign (weak0, pull1) input_pi = pullup_p_en_i ? 1'b1 : 1'bz;
  assign (weak0, pull1) input_ni = pullup_n_en_i ? 1'b1 : 1'bz;
`endif

  assign input_o = (input_en_i) ? input_p & ~input_n : 1'b0;

  prim_buf obs_buf (
    .in_i  (input_o),
    .out_o (usb_diff_rx_obs_o)
  );

endmodule : prim_generic_usb_diff_rx
