// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Link state detection
//

`include "prim_assert.sv"

module usbdev_linkstate (
  input  logic clk_48mhz_i,
  input  logic rst_ni,
  input  logic us_tick_i,
  input  logic usb_sense_i,
  input  logic usb_dp_i,
  input  logic usb_dn_i,
  input  logic usb_oe_i,
  input  logic usb_pullup_en_i,
  input  logic rx_idle_det_i,
  input  logic rx_j_det_i,
  input  logic sof_valid_i,
  input  logic resume_link_active_i, // pulse

  output logic link_disconnect_o,  // level
  output logic link_powered_o,     // level
  output logic link_reset_o,       // level
  output logic link_active_o,      // level
  output logic link_suspend_o,     // level
  output logic link_resume_o,      // pulse
  output logic host_lost_o,        // level
  output logic sof_missed_o,       // pulse

  output logic [2:0] link_state_o
);

  // Suspend signaling is 3ms of J by spec.
  localparam logic [11:0] SUSPEND_TIMEOUT = 12'd3000;
  // Reset is 2.5us - 10ms of SE0 by spec, though care should be taken to not
  // confuse the 2 *low-speed* bit times (1.33us) of SE0 that terminate resume
  // signaling. Use 3us here.
  localparam logic [2:0]  RESET_TIMEOUT   = 3'd3;
  // Consider an SOF lost after 1.005 ms. The extra 5 us helps accommodate
  // the worst case frequency difference between the host and device, due to a
  // +/- 2500 ppm range around 12 MHz.
  localparam logic [9:0]  SOF_TIMEOUT     = 10'd1005;

  typedef enum logic [2:0] {
    // No power and/or no pull-up connected state
    LinkDisconnected = 0,
    // Powered / connected states
    LinkPowered = 1,
    LinkPoweredSuspended = 2,
    // Active states
    LinkActiveNoSOF = 5,
    LinkActive = 3,
    LinkSuspended = 4,
    LinkResuming = 6
  } link_state_e;

  typedef enum logic [1:0] {
    NoRst,
    RstCnt,
    RstPend
  } link_rst_state_e;

  typedef enum logic [1:0] {
    Active,
    InactCnt,
    InactPend
  } link_inac_state_e;

  link_state_e  link_state_d, link_state_q;
  logic         see_pwr_sense;

  // Reset FSM
  logic [2:0]      link_rst_timer_d, link_rst_timer_q;
  link_rst_state_e link_rst_state_d, link_rst_state_q;
  logic            link_reset; // reset detected (level)

  // Link inactivity detection
  logic              monitor_inac; // monitor link inactivity
  logic [11:0]       link_inac_timer_d, link_inac_timer_q;
  link_inac_state_e  link_inac_state_d, link_inac_state_q;


  // Events that are not triggered by a timeout
  logic ev_bus_active;

  // Events that are triggered by timeout
  logic ev_bus_inactive, ev_reset;

  assign link_disconnect_o = (link_state_q == LinkDisconnected);
  assign link_powered_o    = see_pwr_sense;
  assign link_suspend_o    = (link_state_q == LinkSuspended ||
    link_state_q == LinkPoweredSuspended);
  assign link_active_o     = (link_state_q == LinkActive) ||
    (link_state_q == LinkActiveNoSOF);
  // Link state is stable, so we can output it to the register
  assign link_state_o      =  link_state_q;

  // If the PHY reflects the line state on rx pins when the device is driving
  // then the usb_oe_i check isn't needed here. But it seems best to do the check
  // to be robust in the face of different PHY designs.
  logic see_se0, line_se0_raw;
  assign line_se0_raw = (usb_dn_i == 1'b0) & (usb_dp_i == 1'b0) & (usb_oe_i == 1'b0);

  // four ticks is a bit time
  // Could completely filter out 2-cycle EOP SE0 here but
  // does not seem needed
  prim_filter #(
    .AsyncOn(0), // No synchronizer required
    .Cycles(6)
  ) filter_se0 (
    .clk_i    (clk_48mhz_i),
    .rst_ni   (rst_ni),
    .enable_i (1'b1),
    .filter_i (line_se0_raw),
    .filter_o (see_se0)
  );

  prim_filter #(
    .AsyncOn(0), // No synchronizer required
    .Cycles(6)
  ) filter_pwr_sense (
    .clk_i    (clk_48mhz_i),
    .rst_ni   (rst_ni),
    .enable_i (1'b1),
    .filter_i (usb_sense_i),
    .filter_o (see_pwr_sense)
  );

  // Simple events
  assign ev_bus_active = !rx_idle_det_i;

  assign monitor_inac = see_pwr_sense ? ((link_state_q == LinkPowered) | link_active_o) :
                        1'b0;

  always_comb begin
    link_state_d = link_state_q;
    link_resume_o = 0;

    // If VBUS ever goes away the link has disconnected (likewise if the
    // pull-up goes away / user requested disconnection)
    if (!see_pwr_sense || !usb_pullup_en_i) begin
      link_state_d = LinkDisconnected;
    end else begin
      unique case (link_state_q)
        // No USB supply detected (USB spec: Attached)
        LinkDisconnected: begin
          if (see_pwr_sense & usb_pullup_en_i) begin
            link_state_d = LinkPowered;
          end
        end

        LinkPowered: begin
          if (ev_reset) begin
            link_state_d = LinkActiveNoSOF;
          end else if (resume_link_active_i) begin
            // Software-directed jump to resume from LinkSuspended, in case
            // this module was previously powered down.
            link_state_d = LinkResuming;
          end else if (ev_bus_inactive) begin
            link_state_d = LinkPoweredSuspended;
          end
        end

        LinkPoweredSuspended: begin
          if (ev_reset) begin
            link_state_d = LinkActiveNoSOF;
          end else if (ev_bus_active) begin
            link_resume_o = 1;
            link_state_d  = LinkPowered;
          end
        end

        // An event occurred that brought the link out of LinkSuspended, but
        // the end-of-resume signaling may not have occurred yet.
        // Park here before starting to count towards not seeing SOF. Wait for
        // the end of resume signaling before expecting SOF. The host will
        // return the link to idle after a low-speed EOP. Instead of trying to
        // capture the termination of resume signaling direclty, wait for
        // any J / idle symbol (or a bus reset).
        LinkResuming: begin
          if (rx_j_det_i | ev_reset) begin
            link_resume_o = 1;
            link_state_d = LinkActiveNoSOF;
          end
        end

        // Active but not yet seen a frame
        // One reason for getting stuck here is the host thinks it is a LS link
        // which could happen if the flipped bit does not match the actual pins
        // Annother is the SI is bad so good data is not recovered from the link
        LinkActiveNoSOF: begin
          if (ev_bus_inactive) begin
            link_state_d = LinkSuspended;
          end else if (sof_valid_i) begin
            link_state_d = LinkActive;
          end
        end

        // Active (USB spec: Default / Address / Configured)
        LinkActive: begin
          if (ev_bus_inactive) begin
            link_state_d = LinkSuspended;
          end else if (ev_reset) begin
            link_state_d = LinkActiveNoSOF;
          end
        end

        LinkSuspended: begin
          if (ev_reset) begin
            link_resume_o = 1;
            link_state_d  = LinkActiveNoSOF;
          end else if (ev_bus_active) begin
            link_state_d  = LinkResuming;
          end
        end

        default: begin
          link_state_d = LinkDisconnected;
        end
      endcase // case (link_state_q)
    end
  end

  `ASSERT(LinkStateValid_A, link_state_q inside {LinkDisconnected, LinkPowered,
    LinkPoweredSuspended, LinkResuming, LinkActiveNoSOF, LinkActive, LinkSuspended}, clk_48mhz_i)

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      link_state_q <= LinkDisconnected;
    end else begin
      link_state_q <= link_state_d;
    end
  end

  /////////////////////
  // Reset detection //
  /////////////////////
  //  Here we clean up the SE0 signal and generate a single ev_reset at
  //  the end of a valid reset

  always_comb begin : proc_rst_fsm
    link_rst_state_d  = link_rst_state_q;
    link_rst_timer_d  = link_rst_timer_q;
    ev_reset          = 1'b0;
    link_reset        = 1'b0;

    unique case (link_rst_state_q)
      // No reset signal detected
      NoRst: begin
        if (see_se0) begin
          link_rst_state_d = RstCnt;
          link_rst_timer_d = 0;
        end
      end

      // Reset signal detected -> counting
      RstCnt: begin
        if (!see_se0) begin
          link_rst_state_d = NoRst;
        end else begin
          if (us_tick_i) begin
            if (link_rst_timer_q == RESET_TIMEOUT) begin
              link_rst_state_d = RstPend;
            end else begin
              link_rst_timer_d = link_rst_timer_q + 1;
            end
          end
        end
      end

      // Detected reset -> wait for falling edge
      RstPend: begin
        if (!see_se0) begin
          link_rst_state_d = NoRst;
          ev_reset = 1'b1;
        end
        link_reset = 1'b1;
      end

      default : link_rst_state_d = NoRst;
    endcase
  end

  `ASSERT(LinkRstStateValid_A, link_rst_state_q inside {NoRst, RstCnt, RstPend}, clk_48mhz_i)

  assign link_reset_o = link_reset;

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin : proc_reg_rst
    if (!rst_ni) begin
      link_rst_state_q <= NoRst;
      link_rst_timer_q <= 0;
    end else begin
      link_rst_state_q <= link_rst_state_d;
      link_rst_timer_q <= link_rst_timer_d;
    end
  end

  ////////////////////
  // Idle detection //
  ////////////////////
  //  Here we clean up the idle signal and generate a single ev_bus_inactive
  //  after the timer expires
  always_comb begin : proc_idle_det
    link_inac_state_d = link_inac_state_q;
    link_inac_timer_d = link_inac_timer_q;
    ev_bus_inactive   = 0;

    unique case (link_inac_state_q)
      // Active or disabled
      Active: begin
        link_inac_timer_d = 0;
        if (!ev_bus_active && monitor_inac) begin
          link_inac_state_d = InactCnt;
        end
      end

      // Got an inactivity signal -> count duration
      InactCnt: begin
        if (ev_bus_active || !monitor_inac) begin
          link_inac_state_d  = Active;
        end else if (us_tick_i) begin
          if (link_inac_timer_q == SUSPEND_TIMEOUT) begin
            link_inac_state_d = InactPend;
            ev_bus_inactive = 1;
          end else begin
            link_inac_timer_d = link_inac_timer_q + 1;
          end
        end
      end

      // Counter expired & event sent, wait here
      InactPend: begin
        if (ev_bus_active || !monitor_inac) begin
          link_inac_state_d  = Active;
        end
      end

      default : link_inac_state_d = Active;
    endcase
  end

  `ASSERT(LincInacStateValid_A, link_inac_state_q inside {Active, InactCnt, InactPend}, clk_48mhz_i)

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin : proc_reg_idle_det
    if (!rst_ni) begin
      link_inac_state_q <= Active;
      link_inac_timer_q <= 0;
    end else begin
      link_inac_state_q <= link_inac_state_d;
      link_inac_timer_q <= link_inac_timer_d;
    end
  end

  /////////////////////////////////////////
  // Host loss and missing sof detection //
  /////////////////////////////////////////
  // sof_missed if no SOF was observed in 1.005ms and the link is active
  // host_lost if 4 frames have gone by without observing a SOF
  logic [2:0] missed_sof_count;
  logic [9:0] missing_sof_timer;

  assign host_lost_o = missed_sof_count[2];
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      missed_sof_count <= '0;
    end else begin
      if (sof_valid_i || !link_active_o || link_reset) begin
        missed_sof_count <= '0;
      end else if (sof_missed_o && !host_lost_o) begin
        missed_sof_count <= missed_sof_count + 1;
      end
    end
  end

  assign sof_missed_o = (missing_sof_timer == SOF_TIMEOUT);
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      missing_sof_timer <= '0;
    end else begin
      if (sof_missed_o || sof_valid_i || !link_active_o || link_reset) begin
        missing_sof_timer <= '0;
      end else if (us_tick_i) begin
        missing_sof_timer <= missing_sof_timer + 1;
      end
    end
  end
endmodule
