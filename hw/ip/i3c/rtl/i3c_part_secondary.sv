// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// I3C top level wrapper for OpenTitan, secondary partition of the split IP.
//
// - Target Reset Detector, which may be placed in an Always On power domain.

`include "prim_assert.sv"

module i3c_part_secondary
  import i3c_pkg::*;
(
  // Always ON domain clock and reset.
  input                   clk_aon_i,
  input                   rst_aon_ni,

  // SCL and SDA, observed by the Target Reset Detector.
  input                   cio_rstdet_scl_i,
  input                   cio_rstdet_sda_i,

  // Request/response from/to the primary partition.
  input                   rstdet_enable_i,
  input  i3c_rstdet_req_t rstdet_i,
  output i3c_rstdet_rsp_t rstdet_o,

  // Wake-up request to the power manager.
  output logic            rstdet_wkup_req_o,
  // Reset request for the I3C peripheral.
  output logic            rstdet_target_rst_o
);

  i3c_reset_detector u_reset_detector (
    .clk_aon_i      (clk_aon_i),
    .rst_aon_ni     (rst_aon_ni),

    .enable_i       (rstdet_enable_i),

    .req_i          (rstdet_i),
    .rsp_o          (rstdet_o),

    .scl_i          (cio_rstdet_scl_i),
    .sda_i          (cio_rstdet_sda_i),

    .wake_up_o      (rstdet_wkup_req_o),
    .target_reset_o (rstdet_target_rst_o),
    // An external Controller must not be able to reset the entire chip, so the chip reset
    // request is not exposed.
    .chip_reset_o   (),

    // TODO(#31335): scan support; scan/DFT signals are only available in the primary partition.
    .scan_clk_i     (1'b0),
    .scanmode_i     (prim_mubi_pkg::MuBi4False)
  );

  // Assert Known for outputs.
  `ASSERT_KNOWN(RstDetRspKnown_A, rstdet_o, clk_aon_i, !rst_aon_ni)
  `ASSERT_KNOWN(RstDetWkupReqKnown_A, rstdet_wkup_req_o, clk_aon_i, !rst_aon_ni)
  `ASSERT_KNOWN(RstDetTargetRstKnown_A, rstdet_target_rst_o, clk_aon_i, !rst_aon_ni)

endmodule
