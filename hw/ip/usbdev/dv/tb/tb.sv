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

  wire aon_clk, aon_rst_n;
  wire usb_clk, usb_rst_n;
  wire devmode;
  wire intr_pkt_received;
  wire intr_pkt_sent;
  wire intr_powered;
  wire intr_disconnected;
  wire intr_host_lost;
  wire intr_link_reset;
  wire intr_link_suspend;
  wire intr_link_resume;
  wire intr_av_empty;
  wire intr_rx_full;
  wire intr_av_overflow;
  wire intr_link_in_err;
  wire intr_link_out_err;
  wire intr_rx_crc_err;
  wire intr_rx_pid_err;
  wire intr_rx_bitstuff_err;
  wire intr_frame;

  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if aon_clk_rst_if(.clk(aon_clk), .rst_n(aon_rst_n));
  clk_rst_if usb_clk_rst_if(.clk(usb_clk), .rst_n(usb_rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  pins_if #(1) devmode_if(devmode);
  tl_if tl_if(.clk(usb_clk), .rst_n(usb_rst_n));
  usb20_if usb20_if();

 `DV_ALERT_IF_CONNECT(usb_clk, usb_rst_n)

  // dut
  usbdev dut (
    .clk_i                (usb_clk    ),
    .rst_ni               (usb_rst_n  ),
    .clk_aon_i            (aon_clk    ),
    .rst_aon_ni           (aon_rst_n  ),

    .tl_i                 (tl_if.h2d  ),
    .tl_o                 (tl_if.d2h  ),

    .alert_rx_i           (alert_rx   ),
    .alert_tx_o           (alert_tx   ),

    // USB Interface
    // TOOD: need to hook up an interface
    .cio_usb_dp_i           (1'b1),
    .cio_usb_dn_i           (1'b0),
    .usb_rx_d_i             (1'b0),
    .cio_usb_dp_o           (),
    .cio_usb_dp_en_o        (),
    .cio_usb_dn_o           (),
    .cio_usb_dn_en_o        (),
    .usb_tx_d_o             (),
    .usb_tx_se0_o           (),

    .cio_sense_i            (1'b0),
    .usb_dp_pullup_o        (),
    .usb_dn_pullup_o        (),
    .usb_rx_enable_o        (),
    .usb_tx_use_d_se0_o     (),

    // Direct pinmux aon detect connections
    .usb_aon_suspend_req_o  (),
    .usb_aon_wake_ack_o     (),

    // Events and debug info from wakeup module
    .usb_aon_bus_reset_i          ('0),
    .usb_aon_sense_lost_i         ('0),
    .usb_aon_wake_detect_active_i ('0),

    // SOF reference for clock calibration
    .usb_ref_val_o          (),
    .usb_ref_pulse_o        (),

    // memory configuration
    .ram_cfg_i              ('0),

    // Interrupts
    .intr_pkt_received_o    (intr_pkt_received    ),
    .intr_pkt_sent_o        (intr_pkt_sent        ),
    .intr_powered_o         (intr_powered       ),
    .intr_disconnected_o    (intr_disconnected    ),
    .intr_host_lost_o       (intr_host_lost       ),
    .intr_link_reset_o      (intr_link_reset      ),
    .intr_link_suspend_o    (intr_link_suspend    ),
    .intr_link_resume_o     (intr_link_resume     ),
    .intr_av_empty_o        (intr_av_empty        ),
    .intr_rx_full_o         (intr_rx_full         ),
    .intr_av_overflow_o     (intr_av_overflow     ),
    .intr_link_in_err_o     (intr_link_in_err     ),
    .intr_link_out_err_o    (intr_link_out_err    ),
    .intr_rx_crc_err_o      (intr_rx_crc_err      ),
    .intr_rx_pid_err_o      (intr_rx_pid_err      ),
    .intr_rx_bitstuff_err_o (intr_rx_bitstuff_err ),
    .intr_frame_o           (intr_frame           )
  );

  // Hook up the interrupt pins to the intr_if
  assign interrupts[IntrPktReceived]    = intr_pkt_received;
  assign interrupts[IntrPktSent]        = intr_pkt_sent;
  assign interrupts[IntrPowered]        = intr_powered;
  assign interrupts[IntrDisconnected]   = intr_disconnected;
  assign interrupts[IntrHostLost]       = intr_host_lost;
  assign interrupts[IntrLinkReset]      = intr_link_reset;
  assign interrupts[IntrLinkSuspend]    = intr_link_suspend;
  assign interrupts[IntrLinkResume]     = intr_link_resume;
  assign interrupts[IntrAvEmpty]        = intr_av_empty;
  assign interrupts[IntrRxFull]         = intr_rx_full;
  assign interrupts[IntrAvOverflow]     = intr_av_overflow;
  assign interrupts[IntrLinkInErr]      = intr_link_in_err;
  assign interrupts[IntrLinkOutErr]     = intr_link_out_err;
  assign interrupts[IntrRxCrcErr]       = intr_rx_crc_err;
  assign interrupts[IntrRxPidErr]       = intr_rx_pid_err;
  assign interrupts[IntrRxBitstuffErr]  = intr_rx_bitstuff_err;
  assign interrupts[IntrFrame]          = intr_frame;

  initial begin
    // drive clk and rst_n from clk_if
    aon_clk_rst_if.set_active();
    usb_clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", usb_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "aon_clk_rst_vif", aon_clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual usb20_if)::set(null, "*.env.m_usb20_agent*", "vif", usb20_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
