// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import usbdev_env_pkg::*;
  import usbdev_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire usb_clk, usb_rst_n;
  wire devmode;
  wire intr_pkt_received;
  wire intr_pkt_sent;
  wire intr_connected;
  wire intr_disconnected;
  wire intr_host_lost;
  wire intr_link_reset;
  wire intr_link_suspend;
  wire intr_link_resume;
  wire intr_av_empty;
  wire intr_rx_full;
  wire intr_av_overflow;
  wire intr_link_in_err;
  wire intr_rx_crc_err;
  wire intr_rx_pid_err;
  wire intr_rx_bitstuff_err;
  wire intr_frame;

  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  clk_rst_if usb_clk_rst_if(.clk(usb_clk), .rst_n(usb_rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  usb20_if usb20_if();

  // dut
  usbdev dut (
    .clk_i                (clk        ),
    .rst_ni               (rst_n      ),

    .clk_usb_48mhz_i      (usb_clk    ),
    .rst_usb_48mhz_ni     (usb_rst_n  ),

    .tl_i                 (tl_if.h2d  ),
    .tl_o                 (tl_if.d2h  ),

    // USB Interface
    // TOOD: need to hook up an interface
    .cio_sense_i          (1'b0),
    .cio_d_i              (1'b0),
    .cio_dp_i             (1'b1),
    .cio_dn_i             (1'b0),

    .cio_se0_o            (),
    .cio_se0_en_o         (),
    .cio_dp_pullup_o      (),
    .cio_dp_pullup_en_o   (),
    .cio_dn_pullup_o      (),
    .cio_dn_pullup_en_o   (),
    .cio_tx_mode_se_o     (),
    .cio_tx_mode_se_en_o  (),
    .cio_suspend_o        (),
    .cio_suspend_en_o     (),
    .cio_d_o              (),
    .cio_d_en_o           (),
    .cio_dp_o             (),
    .cio_dp_en_o          (),
    .cio_dn_o             (),
    .cio_dn_en_o          (),

    // Interrupts
    .intr_pkt_received_o    (intr_pkt_received    ),
    .intr_pkt_sent_o        (intr_pkt_sent        ),
    .intr_connected_o       (intr_connected       ),
    .intr_disconnected_o    (intr_disconnected    ),
    .intr_host_lost_o       (intr_host_lost       ),
    .intr_link_reset_o      (intr_link_reset      ),
    .intr_link_suspend_o    (intr_link_suspend    ),
    .intr_link_resume_o     (intr_link_resume     ),
    .intr_av_empty_o        (intr_av_empty        ),
    .intr_rx_full_o         (intr_rx_full         ),
    .intr_av_overflow_o     (intr_av_overflow     ),
    .intr_link_in_err_o     (intr_link_in_err     ),
    .intr_rx_crc_err_o      (intr_rx_crc_err      ),
    .intr_rx_pid_err_o      (intr_rx_pid_err      ),
    .intr_rx_bitstuff_err_o (intr_rx_bitstuff_err ),
    .intr_frame_o           (intr_frame           )
  );

  // Hook up the interrupt pins to the intr_if
  assign interrupts[IntrPktReceived]    = intr_pkt_received;
  assign interrupts[IntrPktSent]        = intr_pkt_sent;
  assign interrupts[IntrConnected]      = intr_connected;
  assign interrupts[IntrDisconnected]   = intr_disconnected;
  assign interrupts[IntrHostLost]       = intr_host_lost;
  assign interrupts[IntrLinkReset]      = intr_link_reset;
  assign interrupts[IntrLinkSuspend]    = intr_link_suspend;
  assign interrupts[IntrLinkResume]     = intr_link_resume;
  assign interrupts[IntrAvEmpty]        = intr_av_empty;
  assign interrupts[IntrRxFull]         = intr_rx_full;
  assign interrupts[IntrAvOverflow]     = intr_av_overflow;
  assign interrupts[IntrLinkInErr]      = intr_link_in_err;
  assign interrupts[IntrRxCrcErr]       = intr_rx_crc_err;
  assign interrupts[IntrRxPidErr]       = intr_rx_pid_err;
  assign interrupts[IntrRxBitstuffErr]  = intr_rx_bitstuff_err;
  assign interrupts[IntrFrame]          = intr_frame;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    usb_clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "usb_clk_rst_vif", usb_clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual usb20_if)::set(null, "*.env.m_usb20_agent*", "vif", usb20_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
