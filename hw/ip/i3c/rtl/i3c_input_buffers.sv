// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Connection and buffering of SCL and SDA signals from the I3C bus into the Target-side logic.
//
// - connection must only occur when the bus is known to be inactive, to prevent traffic being
//   misinterpreted.
// - in particular HDR-DDR traffic could be misinterpreted as spurious Start and stoP signaling.
// - when disconnected, the IP block sees SCL and SDA signals in their idle state, i.e. high.
// - the Target-side logic also monitors the I3C bus via a conventional 2-stage synchronizer and
//   may thus determine when it is safe to connect or disconnect.

module i3c_input_buffers #(
  parameter int unsigned NumSDALanes = 1
) (
  input                     enable_i,

  input                     scl_i,
  input   [NumSDALanes-1:0] sda_i,

  output                    scl_buf_o,
  output                    scl_buf_no,
  output                    sda0_clk_o,
  output                    sda0_clk_no,
  output  [NumSDALanes-1:0] sda_buf_o,

  // DFT-related signals.
  input                     scan_clk_i,
  input                     scanmode_i
);

  // SCL and SDA inputs, and their negations, are used as clocks in some parts of the IP block,
  // and the logic driven also requires a DFT scan chain clock.
  //
  // Additionally, the 'enable_i' signal can be used to protect the logic from disconnected SCL/SDA
  // inputs or other activity when the Target logic is not ready to process traffic, or active
  // traffic could be misinterpreted.

  // Buffered SCL input.
  i3c_clock_buf_en #(
    .OutDisabled  (1'b1),
    .NoFpgaBufG   (1'b0)
  ) u_scl_buf (
    .en_i      (enable_i),
    .clk_i     (scl_i),
    .scanmode_i(scanmode_i),
    .scan_clk_i(scan_clk_i),
    .clk_o     (scl_buf_o)
  );

  // Inverted buffered SCL input.
  i3c_clock_inv_en #(
    .OutDisabled  (1'b0),
    .NoFpgaBufG   (1'b0)
  ) u_scl_inv (
    .en_i      (enable_i),
    .clk_i     (scl_i),
    .scanmode_i(scanmode_i),
    .scan_clk_i(scan_clk_i),
    .clk_no    (scl_buf_no)
  );

  // Buffer SDA input and use it as a clock.
  i3c_clock_buf_en #(
    .OutDisabled  (1'b1),
    .NoFpgaBufG   (1'b0)
  ) u_sda0_clk (
    .en_i      (enable_i),
    .clk_i     (sda_i[0]),
    .scanmode_i(scanmode_i),
    .scan_clk_i(scan_clk_i),
    .clk_o     (sda0_clk_o)
  );

  // Inverted buffered SDA input, used as a clock.
  i3c_clock_inv_en #(
    .OutDisabled  (1'b0),
    .NoFpgaBufG   (1'b0)
  ) u_sda0_clk_n (
    .en_i      (enable_i),
    .clk_i     (sda_i[0]),
    .scanmode_i(scanmode_i),
    .scan_clk_i(scan_clk_i),
    .clk_no    (sda0_clk_no)
  );

  // Data buffering, to avoid SCL-relative skew.
  // TODO: Ensure that this addresses skew, or resort to employing clock buffers here too.
  i3c_buf_en #(
    .Width        (NumSDALanes),
    .OutDisabled  ({NumSDALanes{1'b1}})
  ) u_sda_buf (
    .en_i (enable_i),
    .in_i (sda_i),
    .out_o(sda_buf_o)
  );

endmodule
