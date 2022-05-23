// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Always On USB wake detect
//

`include "prim_assert.sv"

module usbdev_aon_wake import usbdev_pkg::*;(
  input  logic clk_aon_i,
  input  logic rst_aon_ni,

  // These come from the chip pin
  input  logic usb_dp_i,
  input  logic usb_dn_i,
  input  logic usb_sense_i,

  // These come from the IP
  input  logic usbdev_dppullup_en_i,
  input  logic usbdev_dnpullup_en_i,

  // Register signals from the IP, which must already be synchronized to the AON domain.
  input  logic wake_ack_aon_i,
  input  logic suspend_req_aon_i,

  // The I/Os that need to be maintained in low-power mode
  output logic usb_dppullup_en_o,
  output logic usb_dnpullup_en_o,

  // wake/powerup request
  output logic wake_req_aon_o,

  // Event signals that indicate what happened while monitoring
  output logic bus_reset_aon_o,
  output logic sense_lost_aon_o,

  // state debug information
  output logic wake_detect_active_aon_o
);

  // Whether this AON wake detector is active and controlling the pull-ups.
  logic wake_detect_active_d, wake_detect_active_q;

  // Detect whether the USB has moved from an idle state.
  logic not_idle_async;
  logic event_not_idle;

  // In suspend it is the device pullup that sets the line state
  // so if the input value differs then the host is doing something
  // This covers both host generated wake (J->K) and host generated reset (J->SE0)
  // Use of the pullups takes care of pinflipping
  assign not_idle_async = (usb_dp_i != usb_dppullup_en_o) |
                          (usb_dn_i != usb_dnpullup_en_o);

  // aon clock is ~200kHz so 4 cycle filter is about 20us
  // as well as noise debounce this gives the main IP time to detect resume if it didn't turn off
  prim_filter #(
    .AsyncOn(1), // Instantiate 2-stage synchronizer
    .Cycles(4)
  ) filter_activity (
    .clk_i    (clk_aon_i),
    .rst_ni   (rst_aon_ni),
    .enable_i (1'b1),
    .filter_i (not_idle_async),
    .filter_o (event_not_idle)
  );

  // Detect bus reset and VBUS removal events.
  // Hold the detectors in reset when this module is in the idle state, to
  // avoid sampling / hysteresis issues that carry over when the link is
  // active.
  logic se0_async, sense_lost_async;
  logic event_bus_reset, event_sense_lost;
  logic bus_reset_d, bus_reset_q;
  logic sense_lost_d, sense_lost_q;

  assign se0_async = ~usb_dp_i & ~usb_dn_i;
  assign sense_lost_async = ~usb_sense_i;

  prim_filter #(
    .AsyncOn(1),
    .Cycles(3)
  ) filter_bus_reset (
    .clk_i    (clk_aon_i),
    .rst_ni   (rst_aon_ni),
    .enable_i (1'b1),
    .filter_i (se0_async),
    .filter_o (event_bus_reset)
  );

  prim_filter #(
    .AsyncOn(1),
    .Cycles(3)
  ) filter_sense (
    .clk_i    (clk_aon_i),
    .rst_ni   (rst_aon_ni),
    .enable_i (1'b1),
    .filter_i (sense_lost_async),
    .filter_o (event_sense_lost)
  );

  assign bus_reset_d = (event_bus_reset | bus_reset_q) & wake_detect_active_q;
  assign sense_lost_d = (event_sense_lost | sense_lost_q) & wake_detect_active_q;

  assign bus_reset_aon_o = bus_reset_q;
  assign sense_lost_aon_o = sense_lost_q;

  logic wake_req_d, wake_req_q;
  assign wake_req_d = wake_detect_active_q &
                      (event_not_idle | event_bus_reset | event_sense_lost | wake_req_q);
  assign wake_req_aon_o = wake_req_q;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin : proc_reg_events
    if (!rst_aon_ni) begin
      bus_reset_q <= 1'b0;
      sense_lost_q <= 1'b0;
      wake_req_q <= 1'b0;
    end else begin
      bus_reset_q <= bus_reset_d;
      sense_lost_q <= sense_lost_d;
      wake_req_q <= wake_req_d;
    end
  end

  always_comb begin : proc_awk_fsm
    wake_detect_active_d = wake_detect_active_q;

    unique case (wake_detect_active_q)
      // No aon suspend entry has been requested or detected
      1'b0: begin
        if (suspend_req_aon_i) begin
          wake_detect_active_d = 1'b1;
        end
      end

      // The USB IP has passed control to this module for handling the suspend
      // request. wake_ack_i must be asserted to bring control back to the USB
      // IP.
      1'b1: begin
        if (wake_ack_aon_i) begin
          wake_detect_active_d = 1'b0;
        end
      end
      default : wake_detect_active_d = 1'b0;
    endcase
  end

  `ASSERT_KNOWN(WakeDetectActiveAonKnown_A, wake_detect_active_aon_o,
    clk_aon_i, !rst_aon_ni)

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin : proc_reg_awk
    if (!rst_aon_ni) begin
      wake_detect_active_q <= 1'b0;
    end else begin
      wake_detect_active_q <= wake_detect_active_d;
    end
  end

  assign wake_detect_active_aon_o = wake_detect_active_q;

  // Control the pullup enable outputs from the AON module when it's active
  logic usbdev_dppullup_en_aon, usbdev_dnpullup_en_aon;
  logic aon_dppullup_en_d, aon_dppullup_en_q;
  logic aon_dnpullup_en_d, aon_dnpullup_en_q;

  prim_flop_2sync #(
    .Width(2)
  ) u_pullup_en_cdc (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i({usbdev_dppullup_en_i, usbdev_dnpullup_en_i}),
    .q_o({usbdev_dppullup_en_aon, usbdev_dnpullup_en_aon})
  );

  assign aon_dppullup_en_d = wake_detect_active_q ? aon_dppullup_en_q
                                                  : usbdev_dppullup_en_aon;
  assign aon_dnpullup_en_d = wake_detect_active_q ? aon_dnpullup_en_q
                                                  : usbdev_dnpullup_en_aon;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin : proc_reg_pullup_en
    if (!rst_aon_ni) begin
      aon_dppullup_en_q <= 1'b0;
      aon_dnpullup_en_q <= 1'b0;
    end else begin
      aon_dppullup_en_q <= aon_dppullup_en_d;
      aon_dnpullup_en_q <= aon_dnpullup_en_d;
    end
  end

  assign usb_dppullup_en_o = wake_detect_active_q ? aon_dppullup_en_q
                                                  : usbdev_dppullup_en_i;
  assign usb_dnpullup_en_o = wake_detect_active_q ? aon_dnpullup_en_q
                                                  : usbdev_dnpullup_en_i;

endmodule
