// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Always On USB wake detect
//

module usbdev_aon_wake import usbdev_pkg::*;(
  input  logic clk_aon_i,
  input  logic rst_aon_ni,

  // the system to which usb belongs has entered low power
  input  logic low_power_alw_i,

  // These come from the chip pin
  input  logic usb_dp_async_alw_i,
  input  logic usb_dn_async_alw_i,

  // These come from post pinmux sleep handling logic
  input  logic usb_dppullup_en_alw_i,
  input  logic usb_dnpullup_en_alw_i,

  // Register signals from IP
  input  logic usb_out_of_rst_upwr_i,
  input  logic usb_aon_wake_en_upwr_i,
  input  logic usb_aon_woken_upwr_i,

  // Status from IP, must be valid for long enough for aon clock to catch (>15us)
  input  logic usb_suspended_upwr_i,

  // wake/powerup request
  output logic wake_req_alw_o,

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
  assign low_power_async = low_power_alw_i & ~usb_out_of_rst_upwr_i;

  // The suspend_req / wake ack / low power construction come from multiple clock domains.
  // As a result the 2 flop sync could glitch for up to 1 cycle.  Place a filter after
  // the two flop sync to passthrough the value only when stable.
  logic [2:0] filter_cdc_in, filter_cdc_out;
  prim_flop_2sync #(
    .Width (3)
  ) u_cdc_suspend_req (
    .clk_i  (clk_aon_i),
    .rst_ni (rst_aon_ni),
    .d_i    ({low_power_async, suspend_req_async, wake_ack_async}),
    .q_o    (filter_cdc_in)
  );

  for (genvar i = 0; i < 3; i++) begin : gen_filters
    prim_filter #(
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
  assign notidle_async = (usb_dp_async_alw_i != usb_dppullup_en_alw_i) |
                         (usb_dn_async_alw_i != usb_dnpullup_en_alw_i);

  // aon clock is ~200kHz so 4 cycle filter is about 20us
  // as well as noise debounce this gives the main IP time to detect resume if it didn't turn off
  prim_filter #(.Cycles(4)) filter_activity (
    .clk_i    (clk_aon_i),
    .rst_ni   (rst_aon_ni),
    .enable_i (1'b1),
    .filter_i (notidle_async),
    .filter_o (wake_req)
  );

  always_comb begin : proc_awk_fsm
    astate_d  = astate_q;

    unique case (astate_q)
      // No aon suspend entry has been requested or detected
      AwkIdle: begin
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

      // Suspend has been enetered and the USB IP is in low power
      AwkTrigUoff: begin
        if (wake_req) begin
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

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin : proc_reg_awk
    if (!rst_aon_ni) begin
      astate_q <= AwkIdle;
    end else begin
      astate_q <= astate_d;
    end
  end

  assign wake_req_alw_o = (astate_q == AwkWoken);

  assign state_debug_o = astate_q;

endmodule
