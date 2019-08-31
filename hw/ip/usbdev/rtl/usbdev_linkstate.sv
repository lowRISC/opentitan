// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Link state detection
//

module usbdev_linkstate (
  input        clk_48mhz_i,
  input        rst_ni,
  input        us_tick_i,
  input        usb_sense_i,
  input        usb_rx_dp_i,
  input        usb_rx_dn_i,
  input        sof_valid_i,
  output logic link_disconnect_o,
  output logic link_reset_o,
  output logic link_suspend_o,
  output logic link_resume_o,
  output logic [1:0] link_state_o,
  output logic host_lost_o
);

  localparam SUSPEND_TIMEOUT = 12'd3000; // 3ms by spec
  localparam RESET_TIMEOUT   = 12'd3;    // 3us. Can be 2.5us - 10ms by spec

  typedef enum logic [2:0] {
    LinkDisconnect  = 3'h000,
    // Reset state
    LinkReset       = 3'b001,
    // Suspend state
    LinkSuspend     = 3'b010,
    // Active states
    LinkActive      = 3'b100,
    LinkWaitSuspend = 3'b101,
    LinkWaitReset   = 3'b110
  } link_state_e;

  link_state_e  link, link_next;
  logic        link_active, resume_next;
  logic        rx_dp, rx_dn;
  logic        line_se0, line_idle;
  logic        see_se0, see_idle;
  logic [11:0] timeout, timeout_next;
  logic        time_expire, waiting, waiting_next;

  assign link_disconnect_o = (link == LinkDisconnect);
  assign link_reset_o      = (link == LinkReset);
  assign link_suspend_o    = (link == LinkSuspend);
  assign link_active       = (link == LinkActive) |
                             (link == LinkWaitSuspend) |
                             (link == LinkWaitReset);
  // re-encode to enum values from register description
  // (so sw doesn't have to deal with changes between the active states)
  assign link_state_o      = link_disconnect_o ? 2'h0 :
                             link_suspend_o ? 2'h2 :
                             link_reset_o ? 2'h1 : 2'h3;

  prim_flop_2sync #(.Width(2)) syncrx (
    .clk_i (clk_48mhz_i),
    .rst_ni (rst_ni),
    .d ({usb_rx_dp_i, usb_rx_dn_i}),
    .q ({rx_dp, rx_dn})
  );
  assign line_se0 = (rx_dp == 1'b0) & (rx_dn == 1'b0);
  assign line_idle = (rx_dp == 1'b1) & (rx_dn == 1'b0); // same as J

  // four ticks is a bit time
  // Could completely filter out 2-cycle EOP SE0 here but
  // does not seem needed
  prim_filter #(.Cycles(6)) filter_se0 (
    .clk_i    (clk_48mhz_i),
    .rst_ni   (rst_ni),
    .enable_i (1'b1),
    .filter_i (line_se0),
    .filter_o (see_se0)
  );

  prim_filter #(.Cycles(6)) filter_idle (
    .clk_i    (clk_48mhz_i),
    .rst_ni   (rst_ni),
    .enable_i (1'b1),
    .filter_i (line_idle),
    .filter_o (see_idle)
  );

  always_comb begin
    link_next = link;

    // If VBUS ever goes away the link has disconnected
    if (!usb_sense_i) begin
      link_next = LinkDisconnect;
    end else begin
      case (link)
        LinkDisconnect: begin
          if (usb_sense_i) begin
            link_next = LinkReset;
          end
        end

        LinkWaitReset: begin
          if (!see_se0) begin
            link_next = LinkActive;
          end else if (time_expire) begin
            link_next = LinkReset;
          end
        end

        LinkReset: begin
          if (!see_se0) begin
            link_next = LinkActive;
          end
        end

        LinkWaitSuspend: begin
          if (!see_idle) begin
            link_next = LinkActive;
          end else if (time_expire) begin
            link_next = LinkSuspend;
          end
        end

        LinkSuspend: begin
          if (!see_idle) begin
            link_next = LinkActive;
          end
        end

        LinkActive: begin
          if (see_se0) begin
            link_next = LinkWaitReset;
          end else if (see_idle) begin
            link_next = LinkWaitSuspend;
          end
        end

        default: begin
          link_next = LinkDisconnect;
        end
      endcase // case (link)
    end
  end
  assign waiting_next = (link_next == LinkWaitReset) |
                        (link_next == LinkWaitSuspend);
  assign timeout_next = (link_next == LinkWaitReset) ? RESET_TIMEOUT : SUSPEND_TIMEOUT;
  assign resume_next = (link == LinkSuspend) & (link_next == LinkActive);

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      link <= LinkDisconnect;
      timeout <= '0;
      waiting <= 1'b0;
      link_resume_o <= 1'b0;
    end else begin
      link <= link_next;
      timeout <= timeout_next;
      waiting <= waiting_next;
      link_resume_o <= resume_next;
    end
  end

  logic [11:0] activity_timer; // Max timeout 3ms == 3000us

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      activity_timer <= '0;
      time_expire <= 1'b0;
    end else begin
      if (!waiting) begin
        activity_timer <= '0;
        time_expire <= 1'b0;
      end else if (activity_timer > timeout) begin
        time_expire <= 1'b1;
      end else if (us_tick_i) begin
        activity_timer <= activity_timer + 1'b1;
      end
    end
  end

  // host_lost if no sof in 4.096ms (supposed to be every 1ms)
  // and the link is active
  logic [12:0] host_presence_timer;

  assign host_lost_o = host_presence_timer[12];
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      host_presence_timer <= '0;
    end else begin
      if (sof_valid_i || !link_active) begin
        host_presence_timer <= '0;
      end else if (us_tick_i && !host_lost_o) begin
        host_presence_timer <= host_presence_timer + 1'b1;
      end
    end
  end

endmodule
