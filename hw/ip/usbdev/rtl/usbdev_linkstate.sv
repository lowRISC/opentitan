// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Link state detection
//

module usbdev_linkstate (
  input  logic clk_48mhz_i,
  input  logic rst_ni,
  input  logic us_tick_i,
  input  logic usb_sense_i,
  input  logic usb_dp_i,
  input  logic usb_dn_i,
  input  logic usb_oe_i,
  input  logic rx_jjj_det_i,
  input  logic sof_valid_i,
  output logic link_disconnect_o,  // level
  output logic link_connect_o,     // level
  output logic link_reset_o,       // level
  output logic link_active_o,      // level
  output logic link_suspend_o,     // level
  output logic link_resume_o,      // pulse
  output logic host_lost_o,        // level

  output logic [2:0] link_state_o
);

  localparam logic [11:0] SUSPEND_TIMEOUT = 12'd3000; // 3ms by spec
  localparam logic [2:0]  RESET_TIMEOUT   = 3'd3;     // 3us. Can be 2.5us - 10ms by spec

  typedef enum logic [2:0] {
    // Unpowered state
    LinkDisconnect = 0,
    // Powered states
    LinkPowered = 1,
    LinkPoweredSuspend = 2,
    // Active states
    LinkActive = 3,
    LinkActiveNoSOF = 5,
    LinkSuspend = 4
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

  assign link_disconnect_o = (link_state_q == LinkDisconnect);
  assign link_connect_o    = (link_state_q != LinkDisconnect);
  assign link_suspend_o    = (link_state_q == LinkSuspend ||
    link_state_q == LinkPoweredSuspend);
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
  prim_filter #(.Cycles(6)) filter_se0 (
    .clk_i    (clk_48mhz_i),
    .rst_ni   (rst_ni),
    .enable_i (1'b1),
    .filter_i (line_se0_raw),
    .filter_o (see_se0)
  );

  prim_filter #(.Cycles(6)) filter_pwr_sense (
    .clk_i    (clk_48mhz_i),
    .rst_ni   (rst_ni),
    .enable_i (1'b1),
    .filter_i (usb_sense_i),
    .filter_o (see_pwr_sense)
  );

  // Simple events
  assign ev_bus_active = !rx_jjj_det_i;

  assign monitor_inac = see_pwr_sense ? ((link_state_q == LinkPowered) | link_active_o) :
                        1'b0;

  always_comb begin
    link_state_d = link_state_q;
    link_resume_o = 0;

    // If VBUS ever goes away the link has disconnected
    if (!see_pwr_sense) begin
      link_state_d = LinkDisconnect;
    end else begin
      unique case (link_state_q)
        // No USB supply detected (USB spec: Attached)
        LinkDisconnect: begin
          if (see_pwr_sense) begin
            link_state_d = LinkPowered;
          end
        end

        LinkPowered: begin
          if (ev_reset) begin
            link_state_d = LinkActiveNoSOF;
          end else if (ev_bus_inactive) begin
            link_state_d = LinkPoweredSuspend;
          end
        end

        LinkPoweredSuspend: begin
          if (ev_reset) begin
            link_state_d = LinkActiveNoSOF;
          end else if (ev_bus_active) begin
            link_resume_o = 1;
            link_state_d  = LinkPowered;
          end
        end

        // Active but not yet seen a frame
        // One reason for getting stuck here is the host thinks it is a LS link
        // which could happen if the flipped bit does not match the actual pins
        // Annother is the SI is bad so good data is not recovered from the link
        LinkActiveNoSOF: begin
          if (ev_bus_inactive) begin
            link_state_d = LinkSuspend;
          end else if (sof_valid_i) begin
            link_state_d = LinkActive;
          end
        end

        // Active (USB spec: Default / Address / Configured)
        LinkActive: begin
          if (ev_bus_inactive) begin
            link_state_d = LinkSuspend;
          end else if (ev_reset) begin
            link_state_d = LinkActiveNoSOF;
          end
        end

        LinkSuspend: begin
          if (ev_reset) begin
            link_resume_o = 1;
            link_state_d  = LinkActiveNoSOF;
          end else if (ev_bus_active) begin
            link_resume_o = 1;
            link_state_d  = LinkActive;
          end
        end

        default: begin
          link_state_d = LinkDisconnect;
        end
      endcase // case (link_state_q)
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      link_state_q <= LinkDisconnect;
    end else begin
      link_state_q <= link_state_d;
    end
  end

  /////////////////////
  // Reset detection //
  /////////////////////
  //  Here we clean up the SE0 signal and generate a signle ev_reset at
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
  //  Here we clean up the idle signal and generate a signle ev_bus_inactive
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

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin : proc_reg_idle_det
    if (!rst_ni) begin
      link_inac_state_q <= Active;
      link_inac_timer_q <= 0;
    end else begin
      link_inac_state_q <= link_inac_state_d;
      link_inac_timer_q <= link_inac_timer_d;
    end
  end

  /////////////////////////
  // Host loss detection //
  /////////////////////////
  // host_lost if no sof in 4.096ms (supposed to be every 1ms)
  // and the link is active
  logic [12:0] host_presence_timer;

  assign host_lost_o = host_presence_timer[12];
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      host_presence_timer <= '0;
    end else begin
      if (sof_valid_i || !link_active_o || link_reset) begin
        host_presence_timer <= '0;
      end else if (us_tick_i && !host_lost_o) begin
        host_presence_timer <= host_presence_timer + 1;
      end
    end
  end

endmodule
