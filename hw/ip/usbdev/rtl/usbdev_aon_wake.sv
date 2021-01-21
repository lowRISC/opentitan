// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Always On USB wake detect
//

module usbdev_aon_wake import usbdev_pkg::*;(
  input  logic clk_aon_i,
  input  logic rst_aon_ni,

  // signals tagged _upwr_ are only valid when this is set
  input  logic usb_out_of_rst_alw_i,

  // These come from the chip pin
  input  logic usb_dp_async_alw_i,
  input  logic usb_dn_async_alw_i,

  // These come from post pinmux sleep handling logic
  input  logic usb_dppullup_en_alw_i,
  input  logic usb_dnpullup_en_alw_i,

  // Register signals from IP
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

  logic trigger_async, trigger;
  logic wake_ack_async, wake_ack;

  // note the _upwr signals are only valid when usb_out_of_rst_alw_i is set
  assign trigger_async = usb_aon_wake_en_upwr_i & usb_suspended_upwr_i & usb_out_of_rst_alw_i;
  assign wake_ack_async = usb_aon_woken_upwr_i & usb_out_of_rst_alw_i;

  prim_flop_2sync #(
    .Width (2)
  ) cdc_trigger (
    .clk_i  (clk_aon_i),
    .rst_ni (rst_aon_ni),
    .d_i    ({trigger_async, wake_ack_async}),
    .q_o    ({trigger, wake_ack})
  );


  logic notidle_async;
  logic notidle_filtered;
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
    .filter_o (notidle_filtered)
  );

  always_comb begin : proc_awk_fsm
    astate_d  = astate_q;

    unique case (astate_q)
      // No aon suspend entry has been requested or detected
      AwkIdle: begin
        if (trigger) begin
          astate_d = AwkTrigUon;
        end
      end

      // Suspend has been triggered but the USB IP power is still on
      AwkTrigUon: begin
        if (notidle_filtered) begin
          // USP IP may manage the wake
          astate_d = AwkWokenUon;
        end else if (!usb_out_of_rst_alw_i) begin
          astate_d = AwkTrigUoff;
        end
      end

      // Suspend has been triggered and the USB IP is powered off
      AwkTrigUoff: begin
        if (notidle_filtered) begin
          astate_d = AwkWoken;
        end
      end

      // The link went not-idle before the USB IP powered off
      // It could be about to power down, it could manage the wake, or this was a glitch
      AwkWokenUon: begin
        if (wake_ack) begin
          astate_d = AwkIdle;
        end else if (trigger) begin
          astate_d = AwkTrigUon;
        end else if (!usb_out_of_rst_alw_i) begin
          astate_d = AwkWoken;
        end
      end

      // The USB IP was powered down and the link went not-idle, time to wake up
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
