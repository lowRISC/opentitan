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

  // the system to which usb belongs has entered low power
  input  logic low_power_alw_i,

  // These come from the chip pin
  input  logic usb_dp_async_alw_i,
  input  logic usb_dn_async_alw_i,
  input  logic usb_sense_async_alw_i,

  // These come from the IP
  input  logic usb_dppullup_en_upwr_i,
  input  logic usb_dnpullup_en_upwr_i,

  // Register signals from IP
  input  logic usb_out_of_rst_upwr_i,
  input  logic usb_aon_wake_en_upwr_i,
  input  logic usb_aon_woken_upwr_i,

  // Status from IP, must be valid for long enough for aon clock to catch (>15us)
  input  logic usb_suspended_upwr_i,

  // The I/Os that need to be maintained in low-power mode
  output logic usb_dppullup_en_o,
  output logic usb_dnpullup_en_o,

  // wake/powerup request
  output logic wake_req_alw_o,

  // Event signals that indicate what happened while monitoring
  output logic bus_reset_alw_o,
  output logic sense_lost_alw_o,

  // state debug information
  output awk_state_e state_debug_o
);

  awk_state_e astate_d, astate_q;

  logic suspend_req_async, suspend_req;
  logic wake_ack_async, wake_ack;
  logic low_power_async, low_power;

  // note the _upwr signals are only valid when usb_out_of_rst_upwr_i is set
  assign suspend_req_async = usb_aon_wake_en_upwr_i & usb_suspended_upwr_i & usb_out_of_rst_upwr_i;
  assign wake_ack_async = usb_aon_woken_upwr_i & usb_out_of_rst_upwr_i;
  assign low_power_async = low_power_alw_i;

  // The suspend_req / wake ack / low power construction come from multiple clock domains.
  // As a result the 2 flop sync could glitch for up to 1 cycle.  Place a filter after
  // the two flop sync to passthrough the value only when stable.
  logic [2:0] filter_cdc_in, filter_cdc_out;
  assign filter_cdc_in = {low_power_async, suspend_req_async, wake_ack_async};

  for (genvar i = 0; i < 3; i++) begin : gen_filters
    prim_filter #(
      .AsyncOn(1), // Instantiate 2-stage synchronizer
      .Cycles(2)
    ) u_filter (
      .clk_i(clk_aon_i),
      .rst_ni(rst_aon_ni),
      .enable_i(1'b1),
      .filter_i(filter_cdc_in[i]),
      .filter_o(filter_cdc_out[i])
    );
  end

  assign {low_power, suspend_req, wake_ack} = filter_cdc_out;

  logic notidle_async;
  logic wake_req;
  // In suspend it is the device pullup that sets the line state
  // so if the input value differs then the host is doing something
  // This covers both host generated wake (J->K) and host generated reset (J->SE0)
  // Use of the pullups takes care of pinflipping
  assign notidle_async = (usb_dp_async_alw_i != usb_dppullup_en_o) |
                         (usb_dn_async_alw_i != usb_dnpullup_en_o);

  // aon clock is ~200kHz so 4 cycle filter is about 20us
  // as well as noise debounce this gives the main IP time to detect resume if it didn't turn off
  prim_filter #(
    .AsyncOn(1), // Instantiate 2-stage synchronizer
    .Cycles(4)
  ) filter_activity (
    .clk_i    (clk_aon_i),
    .rst_ni   (rst_aon_ni),
    .enable_i (1'b1),
    .filter_i (notidle_async),
    .filter_o (wake_req)
  );

  // Detect bus reset and VBUS removal events.
  // Hold the detectors in reset when this module is in the idle state, to
  // avoid sampling / hysteresis issues that carry over when the link is
  // active.
  logic aon_usb_events_active;
  logic se0_async, sense_lost_async;
  logic event_bus_reset, event_sense_lost;
  logic bus_reset_d, bus_reset_q;
  logic sense_lost_d, sense_lost_q;

  assign se0_async = ~usb_dp_async_alw_i & ~usb_dn_async_alw_i;
  assign sense_lost_async = ~usb_sense_async_alw_i;

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

  assign bus_reset_d = (event_bus_reset | bus_reset_q) & aon_usb_events_active;
  assign sense_lost_d = (event_sense_lost | sense_lost_q) & aon_usb_events_active;

  assign bus_reset_alw_o = bus_reset_q;
  assign sense_lost_alw_o = sense_lost_q;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin : proc_reg_events
    if (!rst_aon_ni) begin
      bus_reset_q <= 1'b0;
      sense_lost_q <= 1'b0;
    end else begin
      bus_reset_q <= bus_reset_d;
      sense_lost_q <= sense_lost_d;
    end
  end

  always_comb begin : proc_awk_fsm
    astate_d  = astate_q;
    aon_usb_events_active = 1'b1;

    unique case (astate_q)
      // No aon suspend entry has been requested or detected
      AwkIdle: begin
        aon_usb_events_active = 1'b0;
        if (suspend_req) begin
          astate_d = AwkTrigUon;
        end
      end

      // Suspend has been requested but the USB IP is still alive.
      // If the system progresses into low power, wait for wakeup request.
      // If before the system progresses into low power the suspend request is lost,
      // go manage the interruption
      AwkTrigUon: begin
        // We are trying to juggle when the usb is no longer detecting resumes.
        // This could be when the usb is in reset, or when the system cuts off
        // clocking to usb.
        // If low power and the suspend request drop at the same time (race condition),
        // prioritize low power since the system is already committed to enter low power.
        if (low_power) begin
          astate_d = AwkTrigUoff;
        end else if (!suspend_req) begin
          astate_d = AwkWokenUon;
        end
      end

      // The link went not-idle before the USB IP powered off
      // It could be about to power down, it could manage the wake, or this was a glitch
      // If wake_ack is seen, that means software already handled the resume.
      // If suspend_req is seen again, it means th1e !suspend_req seen was just a glitch
      // If low power conditions are seen, this means even though there was a glitch / resume,
      // the system went to low power anyways, we should now follow the normal resume routine.
      AwkWokenUon: begin
        if (wake_ack) begin
          astate_d = AwkIdle;
        end else if (suspend_req) begin
          astate_d = AwkTrigUon;
        end else if (low_power) begin
          astate_d = AwkTrigUoff;
        end
      end

      // Suspend has been entered and the USB IP is in low power
      AwkTrigUoff: begin
        // wake_req covers any events on D+/D-, including a bus reset, since
        // it triggers on anything where D+/D- != J. A bus reset would show an
        // SE0 symbol.
        // sense_lost_q covers events on VBUS.
        if (wake_req | sense_lost_q) begin
          astate_d = AwkWoken;
        end
      end

      // The USB IP was in low power and the link went not-idle, time to wake up
      AwkWoken: begin
        if (wake_ack) begin
          astate_d = AwkIdle;
        end
      end

      default : astate_d = AwkIdle;
    endcase
  end

  `ASSERT(StateValid_A, astate_q inside {AwkIdle, AwkTrigUon, AwkWokenUon, AwkTrigUoff, AwkWoken},
    clk_aon_i, !rst_aon_ni)

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin : proc_reg_awk
    if (!rst_aon_ni) begin
      astate_q <= AwkIdle;
    end else begin
      astate_q <= astate_d;
    end
  end

  assign wake_req_alw_o = (astate_q == AwkWoken);

  assign state_debug_o = astate_q;

  // Control the pullup enable outputs from the AON module when it's active
  logic usb_dppullup_en_alw, usb_dnpullup_en_alw;
  logic aon_dppullup_en_d, aon_dppullup_en_q;
  logic aon_dnpullup_en_d, aon_dnpullup_en_q;

  prim_flop_2sync #(
    .Width(2)
  ) u_pullup_en_cdc (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i({usb_dppullup_en_upwr_i, usb_dnpullup_en_upwr_i}),
    .q_o({usb_dppullup_en_alw, usb_dnpullup_en_alw})
  );

  assign aon_dppullup_en_d = aon_usb_events_active ? aon_dppullup_en_q
                                                   : usb_dppullup_en_alw;
  assign aon_dnpullup_en_d = aon_usb_events_active ? aon_dnpullup_en_q
                                                   : usb_dnpullup_en_alw;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin : proc_reg_pullup_en
    if (!rst_aon_ni) begin
      aon_dppullup_en_q <= 1'b0;
      aon_dnpullup_en_q <= 1'b0;
    end else begin
      aon_dppullup_en_q <= aon_dppullup_en_d;
      aon_dnpullup_en_q <= aon_dnpullup_en_d;
    end
  end

  assign usb_dppullup_en_o = aon_usb_events_active ? aon_dppullup_en_q
                                                   : usb_dppullup_en_upwr_i;
  assign usb_dnpullup_en_o = aon_usb_events_active ? aon_dnpullup_en_q
                                                   : usb_dnpullup_en_upwr_i;

  // The wakeup signal is not latched in the pwrmgr so must be held until acked by software
  `ASSERT(UsbWkupStable_A, wake_req_alw_o |=> wake_req_alw_o ||
      $past(wake_ack) && !low_power_alw_i, clk_aon_i, !rst_aon_ni)

endmodule
