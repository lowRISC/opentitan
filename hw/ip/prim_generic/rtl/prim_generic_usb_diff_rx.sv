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
  input wire         input_pi,      // differential input
  input wire         input_ni,      // differential input
  input              input_en_i,    // input buffer enable
  input              core_pok_i,    // core power indication at VCC level
  input              pullup_p_en_i, // pullup enable for P
  input              pullup_n_en_i, // pullup enable for N
  input [CalibW-1:0] calibration_i, // calibration input
  output logic       input_o        // output of differential input buffer
);

  assign input_o = (input_en_i) ? input_pi & ~input_ni : 1'b0;

  logic unused_pullup_p_en, unused_pullup_n_en;
  logic [CalibW-1:0] unused_calibration;
  logic unused_core_pok;

  assign unused_calibration = calibration_i;
  assign unused_pullup_p_en = pullup_p_en_i;
  assign unused_pullup_n_en = pullup_n_en_i;
  assign unused_core_pok = core_pok_i;

endmodule : prim_generic_usb_diff_rx
