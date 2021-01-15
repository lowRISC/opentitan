// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Always On USB wake detect
//

module usbdev_aon_wake #(
  parameter int NUsbDevPads = 2
) (
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

  // These I/O enables come from the IP and need to be held when IP is off
  //input logic[NUsbDevPads-1:0] usb_o_upwr_i,
  //input logic[NUsbDevPads-1:0] usb_oe_upwr_i,

  // Register signals from IP
  input  logic usb_aon_wake_en_upwr_i,
  input  logic usb_aon_woken_upwr_i,

  // Status from IP, must be valid for long enough for aon clock to catch (>15us)
  input  logic usb_suspended_upwr_i,

  // Pass through to the pins
  //output logic[NUsbDevPads-1:0] usb_o_alw_o,
  //output logic[NUsbDevPads-1:0] usb_oe_alw_o,

  // wake/powerup request
  output logic wake_req_alw_o
);

  // Code the state values so that the transitions software could poll are single bit
  // Woken->Idle and WokenUon->Idle (after sw ack) should therefore be single bit changes
  typedef enum logic [2:0] {
    AwkIdle =     3'b000,
    AwkTrigUon =  3'b011,   // 2 bit change from Idle but sw not monitoring
    AwkTrigUoff = 3'b010,   // ok with two bit change out because chip power is off
    AwkWokenUon = 3'b001,   // one bit change in/out to TrigUon and Idle, chip off to Woken
    AwkWoken =    3'b100    // one bit change out to Idle, in has chip power off
  } awk_state_e;

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

//  // Since pullup signals are static could make capture_ios = ~hold_ios
//  // This ensures capture flop will be holding value before mux swings
//  // astate_q           I I I I T T T
//  // astate_d           I I I T T T T
//  // capture_ios        Y Y Y n n n n
//  // hold_ios           n n n n Y Y Y
//  // d?pullup_en        1 2 3 4 5 6 7 actually static
//  // held_d?pullup_en     1 2 3 3 3 3
//  // d?pullup_en_alw_o  1 2 3 4 3 3 3
//  // hold_ios
//  logic capture_ios, hold_ios;
//  logic dppullup_en, dnpullup_en;
//  logic held_dppullup_en, held_dnpullup_en;
//
//  assign capture_ios = (astate_q == AwkIdle) && (astate_d == AwkIdle);
//  assign hold_ios = (astate_q != AwkIdle);
//
//  // The pullup signals are static while the USB interface is in use
//  // so no need to worry about cdc delays here
//  prim_flop_2sync #(
//    .Width (2)
//  ) cdc_to_aon (
//    .clk_i  (clk_aon_i),
//    .rst_ni (rst_aon_ni),
//    .d_i    ({usb_dppullup_en_upwr_i, usb_dnpullup_en_upwr_i}),
//    .q_o    ({dppullup_en, dnpullup_en})
//  );
//
//  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
//    if (!rst_aon_ni) begin
//      held_dppullup_en <= 0;
//      held_dnpullup_en <= 0;
//    end else begin
//      held_dppullup_en <= capture_ios ? dppullup_en : held_dppullup_en;
//      held_dnpullup_en <= capture_ios ? dnpullup_en : held_dnpullup_en;
//    end
//  end
//
//  prim_generic_clock_mux2 #(
//    .NoFpgaBufG(1)
//  ) i_mux_dppullup_en (
//    .clk0_i (usb_dppullup_en_upwr_i),
//    .clk1_i (held_dppullup_en),
//    .sel_i  (hold_ios),
//    .clk_o  (usb_dppullup_en_alw_o)
//  );
//
//  prim_generic_clock_mux2 #(
//    .NoFpgaBufG(1)
//  ) i_mux_dnpullup_en (
//    .clk0_i (usb_dnpullup_en_upwr_i),
//    .clk1_i (held_dnpullup_en),
//    .sel_i  (hold_ios),
//    .clk_o  (usb_dnpullup_en_alw_o)
//  );
//
//  // outputs never enabled when in suspend with USB IP powered off
//  // the _en_upwr signals will always be 0 when suspend is detected so no glitch
//  // (would this be cleaner as _en_alw_o = _en_upwr_i & !hold_ios)
//  assign usb_dp_en_alw_o = hold_ios ? 0 : usb_dp_en_upwr_i;
//  assign usb_dn_en_alw_o = hold_ios ? 0 : usb_dn_en_upwr_i;
//  assign usb_d_en_alw_o  = hold_ios ? 0 : usb_d_en_upwr_i;

endmodule
