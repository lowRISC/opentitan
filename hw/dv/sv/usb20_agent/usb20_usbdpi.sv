// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module usb20_usbdpi (
  input   clk_i,
  input   rst_ni,

  // Enable DPI module functionality
  input   enable,

  // Outputs from the DPI module
  output  usb_sense_p2d_o,
  output  usb_dp_en_p2d_o,
  output  usb_dn_en_p2d_o,
  output  usb_dp_p2d_o,
  output  usb_dn_p2d_o,

  // Bidirectional, differential bus.
  inout   usb_p,
  inout   usb_n
);

  // Functioning sketch of integration of USBDPI model into dv top-level tb
  // as a connectivity and function test for ASIC

  // This module integrates the existing `usbdpi` module into the DV chip test
  // bench, reconstructing the two unidirectional buses and driver enables that
  // the DPI model requires for its operation, using just the bare bidirectional
  // USB signals.
  //
  // Nomenclature notes:
  //   dp (or p) and dn (or n) are the two signals of the differential USB
  //   d2p means device to DPI
  //   p2d means DPI to device

  ///////////////////////////////////////////////////////////////////////////
  // Simple detection of pull up assertion indicating device presence;
  // we simply respond to the first line to be pulled high by the device after
  // VSENSE assertion, without regard for proper USB 2.0 timing
  ///////////////////////////////////////////////////////////////////////////
  logic usb_pullupdp_d2p;
  logic usb_pullupdn_d2p;

  // Has either pull up been asserted by the device?
  wire usb_pullup_detect = usb_pullupdp_d2p | usb_pullupdn_d2p;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      usb_pullupdp_d2p <= 1'b0;
      usb_pullupdn_d2p <= 1'b0;
    end else if (enable & usb_sense_p2d_o && !usb_pullup_detect) begin
      // Is the FS device pulling DP high?
      if (usb_p === 1'b1) begin
        usb_pullupdp_d2p <= 1'b1;
      end
      // Is the FS device pulling DN high, implying that it has been configured
      // to perform pin-flipping?
      if (usb_n === 1'b1) begin
        usb_pullupdn_d2p <= 1'b1;
      end
    end
  end

  ///////////////////////////////////////////////////////////////////////////
  // Basic activity detection; DPI model indicates whether it is driving,
  // but for the device we must detect a departure from the bus Idle state
  ///////////////////////////////////////////////////////////////////////////
  logic usb_dp_en_d2p_last;
  logic usb_dn_en_d2p_last;
  logic usb_dp_en_d2p;
  logic usb_dn_en_d2p;

  // Idle state of _P and _N bus signals depends upon which pull up has been
  // asserted; the wire that is carrying the true D+ signal will be high
  wire idle_p = usb_pullupdp_d2p;
  wire idle_n = usb_pullupdn_d2p;

  always_comb begin
    usb_dp_en_d2p = usb_dp_en_d2p_last;
    usb_dn_en_d2p = usb_dn_en_d2p_last;
    // Detect transmission start of DPI (it tells us) or device (not already
    // transmitting and there is a departure from the idle state)
    if (usb_dp_en_p2d_o || (!usb_dp_en_d2p && usb_p != idle_p)) begin
      usb_dp_en_d2p = !usb_dp_en_p2d_o;
    end
    if (usb_dn_en_p2d_o || (!usb_dn_en_d2p && usb_n != idle_n)) begin
      usb_dn_en_d2p = !usb_dn_en_p2d_o;
    end
  end

  // Count of 8 SE0 cycles (1/4 bit intervals), followed by a count of 4 Idle
  // (J) cycles. This is just an approximate detection of EOP for the purpose
  // of ascertaining when the device is relinquishing the bus.
  //
  // TODO: In time the DPI model should be modified such that it neither
  // requires nor trusts output enables from the device.
  logic [3:0] se0_cnt;
  logic [1:0] idle_cnt;
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      se0_cnt <= 'b0;
      idle_cnt <= 'b0;
    end else if (enable) begin
      // Count SE0 cycles to detect EOP
      if (usb_p === 1'b0 && usb_n === 1'b0) begin
        se0_cnt <= se0_cnt + 1'b1;
      end else begin
        se0_cnt <= 'b0;
      end
      // Count of Idle (J) cycles because the DPI model needs to see the
      // SE0,SE0,J sequence to perform its own EOP detection.
      if (usb_p == idle_p && usb_n == idle_n) begin
        idle_cnt <= idle_cnt + |{idle_cnt, se0_cnt[3]};
      end else begin
        idle_cnt <= 'b0;
      end
    end
  end

  // 4 idle cycles (1/4 bit intervals) detected after se0_cnt detected 8
  // SE0 cycles (1/4 bit intervals)
  wire eop = &idle_cnt;

  // Assume that the device is driving if the DPI model is not;
  // Note: that we need to ensure the DPI model sees the SE0,SE0,J sequence
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      usb_dp_en_d2p_last <= 1'b0;
      usb_dn_en_d2p_last <= 1'b0;
    end else if (enable & usb_sense_p2d_o & usb_pullup_detect) begin
      // Detect the end of EOP when the device has been transmitting
      if (usb_dp_en_d2p_last & eop) begin
        usb_dp_en_d2p_last <= 1'b0;
      end else begin
        usb_dp_en_d2p_last <= usb_dp_en_d2p;
      end
      // Detect the end of EOP when the device has been transmitting
      if (usb_dn_en_d2p_last & eop) begin
        usb_dn_en_d2p_last <= 1'b0;
      end else begin
        usb_dn_en_d2p_last <= usb_dn_en_d2p;
      end
    end
  end

  // USB DPI
  usbdpi u_usbdpi (
    .clk_i           (clk_i),
    .rst_ni          (rst_ni),
    .clk_48MHz_i     (clk_i),

    .enable          (enable),

    .sense_p2d       (usb_sense_p2d_o),
    .pullupdp_d2p    (usb_pullupdp_d2p),
    .pullupdn_d2p    (usb_pullupdn_d2p),

    .dp_en_p2d       (usb_dp_en_p2d_o),
    .dp_p2d          (usb_dp_p2d_o),
    .dp_d2p          (usb_p),
    .dp_en_d2p       (usb_dp_en_d2p),

    .dn_en_p2d       (usb_dn_en_p2d_o),
    .dn_p2d          (usb_dn_p2d_o),
    .dn_d2p          (usb_n),
    .dn_en_d2p       (usb_dn_en_d2p),

    // ASIC communicates via true differential signaling
    .d_p2d           (),
    .d_d2p           (1'b0),  // not used
    .d_en_d2p        (1'b0),
    .se0_d2p         (1'b0),  // not used
    .rx_enable_d2p   (1'b0),
    .tx_use_d_se0_d2p(1'b0)
  );

endmodule
