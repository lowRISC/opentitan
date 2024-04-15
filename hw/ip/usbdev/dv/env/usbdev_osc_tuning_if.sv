// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface usbdev_osc_tuning_if (
  // Host signals.
  input     host_clk_i,
  input     host_rst_ni,
  // DUT signals.
  input     usb_clk_i,
  input     usb_rst_ni,
  // Reference signal from DUT.
  input     usb_ref_val_i,
  input     usb_ref_pulse_i
);

  // Cycle counters on the host and DUT clocks, to assist with checking of freq/phase vseqs and
  // oscillator tuning; these elapsed cycle counts may be read directly in the waveforms.
  logic [31:0] host_clk_cnt;
  logic [31:0] usb_clk_cnt;
  always_ff @(posedge host_clk_i or negedge host_rst_ni) begin
    if (!host_rst_ni) host_clk_cnt <= 0;
    else host_clk_cnt <= host_clk_cnt + 1'b1;
  end
  always_ff @(posedge usb_clk_i or negedge usb_rst_ni) begin
    if (!usb_rst_ni) usb_clk_cnt <= 0;
    else usb_clk_cnt <= usb_clk_cnt + 1'b1;
  end

  // DUT cycle count at the time of the latest reference pulse.
  bit usb_latest_valid;
  logic [31:0] usb_latest_cnt;

  // Read the DUT cycle delta since the latest sampling point (one bus frame ago),
  // and restart the counting in anticipation of the next reference pulse.
  function automatic integer elapsed_dut_cycles();
    integer delta;
    // Elapsed DUT cycles since the last reference pulse.
    delta = usb_latest_valid ? (usb_clk_cnt - usb_latest_cnt) : 48_000;
    usb_latest_cnt = usb_clk_cnt;
    usb_latest_valid = 1;
    return delta;
  endfunction

endinterface
