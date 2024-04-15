// Copyright lowRISC contributors (OpenTitan project).
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
  `include "cip_macros.svh"

  // Always ON clock and reset (usbdev_aon_wake module)
  wire aon_clk, aon_rst_n;
  // USBDEV clock and reset
  //   (frequency varies to maintain synchronization with the USB host
  wire usb_clk, usb_rst_n;
  // USB Host (usb20_agent or usbdpi) clock and reset
  wire host_clk, host_rst_n;

  wire intr_pkt_received;
  wire intr_pkt_sent;
  wire intr_powered;
  wire intr_disconnected;
  wire intr_host_lost;
  wire intr_link_reset;
  wire intr_link_suspend;
  wire intr_link_resume;
  wire intr_av_out_empty;
  wire intr_rx_full;
  wire intr_av_overflow;
  wire intr_link_in_err;
  wire intr_link_out_err;
  wire intr_rx_crc_err;
  wire intr_rx_pid_err;
  wire intr_rx_bitstuff_err;
  wire intr_frame;
  wire intr_av_setup_empty;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // Physical USB signals.
  wire usb_vbus;
  wire usb_p;
  wire usb_n;
  // Decoded differential signal.
  wire usb_rx_d;

  // Enable for differential receiver.
  wire usb_rx_enable;

  // Pull up enables from usbdev (primary DUT).
  wire usbdev_dp_pullup_en;
  wire usbdev_dn_pullup_en;

  // Pull ups are external to the DUT, and may be controlled by either usbdev (primary DUT)
  // or the usbdev_aon_wake module.
  wire usb_dp_pullup_en;
  wire usb_dn_pullup_en;
  // Driver enables from the DUT.
  wire cio_usb_dp_en;
  wire cio_usb_dn_en;
  // Driven outputs from the DUT.
  wire cio_usb_dp;
  wire cio_usb_dn;

  // Requests from usbdev to usbdev_aon_wake module.
  wire usb_aon_suspend_req;
  wire usb_aon_wake_ack;

  // Event and debug indicators from the usbdev_aon_wake module to usbdev.
  wire usb_aon_bus_not_idle;
  wire usb_aon_bus_reset;
  wire usb_aon_sense_lost;
  wire usb_aon_wake_detect_active;

  // Wake request from AON/Wake to usb20_agent
  wire wake_req_aon;
  // Bus timing reference signals.
  wire usb_ref_val;
  wire usb_ref_pulse;

  // interfaces
  clk_rst_if aon_clk_rst_if(.clk(aon_clk), .rst_n(aon_rst_n));
  clk_rst_if usbdev_clk_rst_if(.clk(usb_clk), .rst_n(usb_rst_n));
  clk_rst_if host_clk_rst_if(.clk(host_clk), .rst_n(host_rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(interrupts);
  tl_if tl_if(.clk(usb_clk), .rst_n(usb_rst_n));
  // This interface models a physical USB connection to a host/USBDPI model.
  usb20_if usb20_if(.clk_i(host_clk), .rst_ni(host_rst_n), .usb_vbus(usb_vbus),
  .usb_p(usb_p), .usb_n(usb_n));
  // This interface is for UVM-based block level DV and has additional connections
  // that may be used to infer the PHY configuration of the DUT and thus exercise all
  // of its configurable input/output modes.
  usb20_block_if usb20_block_if(.clk_i(host_clk), .rst_ni(host_rst_n),
                                .usb_vbus(usb_vbus), .usb_p(usb_p), .usb_n(usb_n));
  `DV_ALERT_IF_CONNECT(usb_clk, usb_rst_n)

  // External differential receiver; USBDEV supports an external differential receiver
  // with USB protocol-compliant robustness against jitter and slew, to produce a clean
  // data signal for sampling into the USBDEV clock domain.
  prim_generic_usb_diff_rx u_usb_diff_rx (
    .input_pi           (usb_p),
    .input_ni           (usb_n),
    .input_en_i         (usb_rx_enable),
    .core_pok_h_i       (1'b1),
    .pullup_p_en_i      (usb_dp_pullup_en),
    .pullup_n_en_i      (usb_dn_pullup_en),
    .calibration_i      ('0),
    .usb_diff_rx_obs_o  (),
    .input_o            (usb_rx_d)
  );

  // DUT
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
    .cio_usb_dp_i           (usb_p),
    .cio_usb_dn_i           (usb_n),
    .usb_rx_d_i             (usb_rx_d),
    .cio_usb_dp_o           (cio_usb_dp                  ),
    .cio_usb_dp_en_o        (cio_usb_dp_en               ),
    .cio_usb_dn_o           (cio_usb_dn                  ),
    .cio_usb_dn_en_o        (cio_usb_dn_en               ),
    .usb_tx_d_o             (usb20_block_if.usb_tx_d_o   ),
    .usb_tx_se0_o           (usb20_block_if.usb_tx_se0_o ),
    .cio_sense_i            (usb_vbus),
    // Pull up enables from primary DUT, but usbdev_aon_wake may override them.
    .usb_dp_pullup_o        (usbdev_dp_pullup_en),
    .usb_dn_pullup_o        (usbdev_dn_pullup_en),
    .usb_rx_enable_o        (usb_rx_enable      ),
    .usb_tx_use_d_se0_o     (usb20_block_if.usb_tx_use_d_se0_o ),
    // Direct pinmux aon detect connections
    .usb_aon_suspend_req_o  (usb_aon_suspend_req),
    .usb_aon_wake_ack_o     (usb_aon_wake_ack),
    // Events and debug info from wakeup module
    .usb_aon_bus_not_idle_i       (usb_aon_bus_not_idle),
    .usb_aon_bus_reset_i          (usb_aon_bus_reset),
    .usb_aon_sense_lost_i         (usb_aon_sense_lost),
    .usb_aon_wake_detect_active_i (usb_aon_wake_detect_active),

    // SOF reference for clock calibration
    .usb_ref_val_o          (usb_ref_val),
    .usb_ref_pulse_o        (usb_ref_pulse),

    // memory configuration
    .ram_cfg_i              ('0),

    // Interrupts
    .intr_pkt_received_o    (intr_pkt_received    ),
    .intr_pkt_sent_o        (intr_pkt_sent        ),
    .intr_powered_o         (intr_powered         ),
    .intr_disconnected_o    (intr_disconnected    ),
    .intr_host_lost_o       (intr_host_lost       ),
    .intr_link_reset_o      (intr_link_reset      ),
    .intr_link_suspend_o    (intr_link_suspend    ),
    .intr_link_resume_o     (intr_link_resume     ),
    .intr_av_out_empty_o    (intr_av_out_empty    ),
    .intr_rx_full_o         (intr_rx_full         ),
    .intr_av_overflow_o     (intr_av_overflow     ),
    .intr_link_in_err_o     (intr_link_in_err     ),
    .intr_link_out_err_o    (intr_link_out_err    ),
    .intr_rx_crc_err_o      (intr_rx_crc_err      ),
    .intr_rx_pid_err_o      (intr_rx_pid_err      ),
    .intr_rx_bitstuff_err_o (intr_rx_bitstuff_err ),
    .intr_frame_o           (intr_frame           ),
    .intr_av_setup_empty_o  (intr_av_setup_empty  )
  );

  // Connections specific to the block-level DV interface.
  assign usb20_block_if.usb_dp_pullup_o = usb_dp_pullup_en;
  assign usb20_block_if.usb_dn_pullup_o = usb_dn_pullup_en;
  assign usb20_block_if.usb_dp_en_o     = cio_usb_dp_en;
  assign usb20_block_if.usb_dn_en_o     = cio_usb_dn_en;
  assign usb20_block_if.usb_dp_o        = cio_usb_dp;
  assign usb20_block_if.usb_dn_o        = cio_usb_dn;
  assign usb20_block_if.wake_req_aon    = wake_req_aon;
  assign usb20_block_if.usb_ref_val_o   = usb_ref_val;
  assign usb20_block_if.usb_ref_pulse_o = usb_ref_pulse;

  // Drivers from the USB device
  assign (strong0, strong1) usb_p = cio_usb_dp_en ? cio_usb_dp : 1'bZ;
  assign (strong0, strong1) usb_n = cio_usb_dn_en ? cio_usb_dn : 1'bZ;
  // Implement pull ups for the physical USB connection to USBDPI model.
  assign (weak0, pull1) usb_p = usb_dp_pullup_en ? 1'b1 : 1'bz;
  assign (weak0, pull1) usb_n = usb_dn_pullup_en ? 1'b1 : 1'bz;

  // Instantiate & connect the USB DPI model for additional block-level testing and coverage.
  usb20_usbdpi u_usb20_usbdpi (
    .clk_i            (host_clk),
    .rst_ni           (host_rst_n),

    .enable           (usb20_if.connected),

    // Outputs from the DPI module
    .usb_sense_p2d_o  (usb20_if.usb_sense_p2d),
    .usb_dp_en_p2d_o  (usb20_if.usb_dp_en_p2d),
    .usb_dn_en_p2d_o  (usb20_if.usb_dn_en_p2d),
    .usb_dp_p2d_o     (usb20_if.usb_dp_p2d),
    .usb_dn_p2d_o     (usb20_if.usb_dn_p2d),

    .usb_p            (usb_p),
    .usb_n            (usb_n)
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
  assign interrupts[IntrAvOutEmpty]     = intr_av_out_empty;
  assign interrupts[IntrRxFull]         = intr_rx_full;
  assign interrupts[IntrAvOverflow]     = intr_av_overflow;
  assign interrupts[IntrLinkInErr]      = intr_link_in_err;
  assign interrupts[IntrLinkOutErr]     = intr_link_out_err;
  assign interrupts[IntrRxCrcErr]       = intr_rx_crc_err;
  assign interrupts[IntrRxPidErr]       = intr_rx_pid_err;
  assign interrupts[IntrRxBitstuffErr]  = intr_rx_bitstuff_err;
  assign interrupts[IntrFrame]          = intr_frame;
  assign interrupts[IntrAvSetupEmpty]   = intr_av_setup_empty;

  // USB Always On Wake module; this module monitors the USB for events whilst usbdev itself is
  // unclocked and/or unpowered.
  usbdev_aon_wake u_usbdev_aon_wake (
    .clk_aon_i                (aon_clk),
    .rst_aon_ni               (aon_rst_n),

    .usb_dp_i                 (usb_p),
    .usb_dn_i                 (usb_n),
    .usb_sense_i              (usb_vbus),

    // Pull up enables from USBDEV
    .usbdev_dppullup_en_i     (usbdev_dp_pullup_en),
    .usbdev_dnpullup_en_i     (usbdev_dn_pullup_en),

    // Requests from USBDEV register configuration
    .wake_ack_aon_i           (usb_aon_wake_ack),
    .suspend_req_aon_i        (usb_aon_suspend_req),

    // Actual pull up enables; driven by usbdev or usbdev_aon_wake
    .usb_dppullup_en_o        (usb_dp_pullup_en),
    .usb_dnpullup_en_o        (usb_dn_pullup_en),

    // Wake request from AON/Wake to usb20_agent
    .wake_req_aon_o           (wake_req_aon),

    .bus_not_idle_aon_o       (usb_aon_bus_not_idle),
    .bus_reset_aon_o          (usb_aon_bus_reset),
    .sense_lost_aon_o         (usb_aon_sense_lost),

    .wake_detect_active_aon_o (usb_aon_wake_detect_active)
  );

  // Monitoring of the host and DUT clocks, to drive oscillator tuning and assist with checking in
  // the freq/phase delta test sequences. This monitoring information is both visible in waveforms
  // and used by the DV to measure the time intervals between assertions of 'usb_ref_pulse_o.'
  //
  // A separate interface performs the monitoring because it is required for use with both
  // 'usb20_agent' and 'usb20_usbdpi.'
  usbdev_osc_tuning_if usbdev_osc_tuning_if (
    // Host signals.
    .host_clk_i       (host_clk),
    .host_rst_ni      (host_rst_n),
    // DUT signals.
    .usb_clk_i        (usb_clk),
    .usb_rst_ni       (usb_rst_n),
    // Timing reference signals.
    .usb_ref_val_i    (usb_ref_val),
    .usb_ref_pulse_i  (usb_ref_pulse)
  );

  initial begin
    // drive clk and rst_n from clk_if
    aon_clk_rst_if.set_active();
    usbdev_clk_rst_if.set_active();
    host_clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", usbdev_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "aon_clk_rst_vif", aon_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "host_clk_rst_vif", host_clk_rst_if);
    uvm_config_db#(virtual usbdev_osc_tuning_if)::set(null, "*.env", "usbdev_osc_tuning_vif",
                   usbdev_osc_tuning_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual usb20_if)::set(null, "*.env", "vif", usb20_if);
    uvm_config_db#(virtual usb20_block_if)::set(null, "*.env.m_usb20_agent*","bif",usb20_block_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
