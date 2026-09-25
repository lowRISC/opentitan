// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// HDR Restart and HDR Exit Pattern detector for I3C Target. It does not have a free-running clock
// of its own, but responds directly to the Controller-supplied SCL signal on the I3C bus.

module i3c_patt_detector (
  // No free-running clock from the IP block core; driven by controller-supplied SCL.
  // Asynchronous reset.
  input         rst_ni,

  // I3C I/O signals being monitored.
  input         scl_buf_i,
  input         sda_clk_i,
  input         sda_clk_ni,

  // Control inputs.
  input         hdr_exit_det_en_i,     // When connected and bus state trusted.
  input         hdr_restart_det_en_i,  // When operating in a supported HDR mode.
  input         hdr_restart_done_i,    // Clear an `hdr_restart_det_o` assertion.

  // HDR pattern detection.
  output        hdr_exit_det_o,
  output logic  hdr_restart_det_o
);

  // The HDR Exit pattern marks the departure from HDR mode and a return to SDR operation.
  // It consists of four falling edges on SDA whilst SCL is held low throughout, followed by
  // a rising edge on SCL. HDR Exit is followed by the standard SDR STOP signaling.
  //     _____   _   _   _   _      __
  // SDA      \_/ \_/ \_/ \_/ \____/
  //     __                       ____   HDR Exit signaling, followed by SDR STOP.
  // SCL   \_____________________/
  //              1   2   3   4    P
  //
  // The HDR Exit pattern must be detected by all I3C devices at all times whilst the Target is
  // enabled, whether or not the HDR mode is supported, because it is used to recover from errors.
  // Since the detection of Start and stoP signaling must be suppressed during HDR modes, it is
  // important to detect any exit from HDR mode in order to re-enable Start and stoP detection.
  //
  // See section 4.3.10.2

  // HDR modes also employ HDR Restart signaling, which is a subset of the HDR Exit pattern,
  // consisting of two SDA falling edges with SCL held low throughout, validated by the rising
  // edge on SCL.
  //                     Possible Restart.
  //     _____   _   _   |______
  // SDA      \_/ \_/ \__/
  //     __                 ____  HDR Restart signaling.
  // SCL   \_______________/
  //              1   2   SCL confirms
  //
  // The HDR Restart pattern serves essentially the same purpose as the Sr (Repeated Start) in
  // SDR mode; it indicates that the Controller is continuing a command and that the bus is not
  // available for arbitration. Only devices that support one or more HDR modes need be capable
  // of detecting this pattern and the detector shall be enabled when a supported HDR mode is used.
  //
  // See section 6.1.2

  // The combined HDR Restart and HDR Exit Detector logic is described in 6.1.2.1.

  import i3c_consts_pkg::*;

  // TODO(#31335): scan mode will need to be able to issue a reset and scan these flops too.

  // SCL low in HDR state enables operation of the Exit and Restart detector.
  wire scl_rst_n = !scl_buf_i & hdr_exit_det_en_i & rst_ni;
  logic [3:0] exit_det;
  always_ff @(posedge sda_clk_ni or negedge scl_rst_n) begin
    if (!scl_rst_n) exit_det <= '0;
    else exit_det <= {exit_det[2:0], 1'b1};
  end

  // HDR Exit pattern detected.
  assign hdr_exit_det_o = exit_det[3];

  // The HDR Restart notification must be reset asynchronously once it has been actioned, without
  // awaiting the next transition on SCL.
  wire restart_rst_n = !hdr_restart_done_i & hdr_restart_det_en_i & rst_ni;

  // Possible Restart means exactly 2 falling edges of SDA and then rising edge of SDA.
  logic poss_restart;
  always_ff @(posedge sda_clk_i or negedge restart_rst_n) begin
    if (!restart_rst_n) poss_restart <= 1'b0;
    else poss_restart <= exit_det[1] & !exit_det[2];
  end

  // A possible restart is confirmed by the rising edge of SCL.
  always_ff @(posedge scl_buf_i or negedge restart_rst_n) begin
    if (!restart_rst_n) hdr_restart_det_o <= 1'b0;
    else hdr_restart_det_o <= poss_restart;
  end

endmodule
