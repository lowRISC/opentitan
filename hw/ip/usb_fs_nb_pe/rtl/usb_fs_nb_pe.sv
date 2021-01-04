// Copyright lowRISC contributors.
// Copyright Luke Valenty (TinyFPGA project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// USB Full Speed Non-Buffered Protocol Engine
//
// Decodes low level USB link protocol from external usb_fs_tx/rx
// Provides upper level with
// - OUT endpoint interface (host to device) which also covers SETUP
// - IN endpoint interface (device to host)
// - Start of Frame interface
//
// Based on usb_fs_pe.v from the TinyFPGA-Bootloader project but
// this version contains no packet buffers

module usb_fs_nb_pe #(
  parameter int unsigned NumOutEps = 2,
  parameter int unsigned NumInEps = 2,
  parameter int unsigned MaxPktSizeByte = 32,
  localparam int unsigned PktW = $clog2(MaxPktSizeByte) // derived parameter
) (
  input  logic                   clk_48mhz_i,
  input  logic                   rst_ni,        // Async. reset, active low
  input  logic                   link_reset_i,  // USB reset, sync to 48 MHz, active high
  input  logic [6:0]             dev_addr_i,

  input  logic                   cfg_eop_single_bit_i, // 1: detect a single SE0 bit as EOP
  input  logic                   cfg_rx_differential_i, // 1: use differential rx data on usb_d_i
  input  logic                   tx_osc_test_mode_i, // Oscillator test mode (constantly output JK)
  input  logic [NumOutEps-1:0]   data_toggle_clear_i, // Clear the data toggles for an EP

  ////////////////////////////
  // USB Endpoint Interface //
  ////////////////////////////
  ///////////////////////////////
  // global endpoint interface //
  ///////////////////////////////

  // out endpoint interfaces
  output logic [3:0]             out_ep_current_o, // Other signals address to this ep
  output logic                   out_ep_data_put_o, // put the data (put addr advances after)
  output logic [PktW - 1:0]      out_ep_put_addr_o, // Offset to put data (0..pktlen)
  output logic [7:0]             out_ep_data_o,
  output logic                   out_ep_newpkt_o,// New OUT pkt start (with in_ep_current_o update)
  output logic                   out_ep_acked_o, // good termination, device has acked
  output logic                   out_ep_rollback_o, // bad termination, discard data
  output logic [NumOutEps-1:0]   out_ep_setup_o,
  input  logic [NumOutEps-1:0]   out_ep_full_i, // Cannot accept data
  input  logic [NumOutEps-1:0]   out_ep_stall_i, // Stalled
  input  logic [NumOutEps-1:0]   out_ep_iso_i, // Configure endpoint in isochronous mode

  // in endpoint interfaces
  output logic [3:0]             in_ep_current_o, // Other signals addressed to this ep
  output logic                   in_ep_rollback_o, // Bad termination, rollback transaction
  output logic                   in_ep_xfr_end_o, // good termination, transaction complete
  output logic                   in_ep_acked_o,   // good term, completed by ack (subset of xfr_end)
  output logic [PktW - 1:0]      in_ep_get_addr_o, // Offset requested (0..pktlen)
  output logic                   in_ep_data_get_o, // Accept data (get_addr advances too)
  output logic                   in_ep_newpkt_o, // New IN pkt start (with in_ep_current_o update)
  input  logic [NumInEps-1:0]    in_ep_stall_i, // Endpoint in a stall state
  input  logic [NumInEps-1:0]    in_ep_has_data_i, // Endpoint has data to supply
  input  logic [7:0]             in_ep_data_i, // Data for current get_addr
  input  logic [NumInEps-1:0]    in_ep_data_done_i, // Set when out of data
  input  logic  [NumInEps-1:0]   in_ep_iso_i, // Configure endpoint in isochronous mode

  // sof interface
  output logic                   sof_valid_o,
  output logic [10:0]            frame_index_o,

  // RX line status
  output logic                   rx_jjj_det_o,

  // RX errors
  output logic                   rx_crc_err_o,
  output logic                   rx_pid_err_o,
  output logic                   rx_bitstuff_err_o,

  ///////////////////////////////////////
  // USB RX Interface (synchronous)    //
  ///////////////////////////////////////
  input  logic                   usb_d_i,
  input  logic                   usb_dp_i,
  input  logic                   usb_dn_i,

  ///////////////////////////////////////
  // USB TX Interface (synchronous)    //
  ///////////////////////////////////////
  output logic                   usb_d_o,
  output logic                   usb_se0_o,
  output logic                   usb_oe_o
);

  import usb_consts_pkg::*;

  // rx interface
  logic bit_strobe;
  logic rx_pkt_start;
  logic rx_pkt_end;
  logic [3:0] rx_pid;
  logic [6:0] rx_addr;
  logic [3:0] rx_endp;
  logic [10:0] rx_frame_num;
  logic rx_data_put;
  logic [7:0] rx_data;
  logic rx_pkt_valid;

  // tx mux
  logic in_tx_pkt_start;
  logic [3:0] in_tx_pid;
  logic out_tx_pkt_start;
  logic [3:0] out_tx_pid;

  // tx interface
  logic tx_pkt_start;
  logic tx_pkt_end;
  logic [3:0] tx_pid;
  logic tx_data_avail;
  logic tx_data_get;
  logic [7:0] tx_data;

  logic usb_oe;

  // sof interface
  assign sof_valid_o = rx_pkt_end & rx_pkt_valid & (usb_pid_e'(rx_pid) == UsbPidSof);
  assign frame_index_o = rx_frame_num;
  assign usb_oe_o = usb_oe;

  usb_fs_nb_in_pe #(
    .NumInEps           (NumInEps),
    .MaxInPktSizeByte   (MaxPktSizeByte)
  ) u_usb_fs_nb_in_pe (
    .clk_48mhz_i           (clk_48mhz_i),
    .rst_ni                (rst_ni),
    .link_reset_i          (link_reset_i),
    .dev_addr_i            (dev_addr_i),

    // endpoint interface
    .in_ep_current_o       (in_ep_current_o),
    .in_ep_rollback_o      (in_ep_rollback_o),
    .in_ep_xfr_end_o       (in_ep_xfr_end_o),
    .in_ep_acked_o         (in_ep_acked_o),
    .in_ep_get_addr_o      (in_ep_get_addr_o),
    .in_ep_data_get_o      (in_ep_data_get_o),
    .in_ep_newpkt_o        (in_ep_newpkt_o),
    .in_ep_stall_i         (in_ep_stall_i),
    .in_ep_has_data_i      (in_ep_has_data_i),
    .in_ep_data_i          (in_ep_data_i),
    .in_ep_data_done_i     (in_ep_data_done_i),
    .in_ep_iso_i           (in_ep_iso_i),

    .data_toggle_clear_i   (data_toggle_clear_i),

    // rx path
    .rx_pkt_start_i        (rx_pkt_start),
    .rx_pkt_end_i          (rx_pkt_end),
    .rx_pkt_valid_i        (rx_pkt_valid),
    .rx_pid_i              (rx_pid),
    .rx_addr_i             (rx_addr),
    .rx_endp_i             (rx_endp),

    // tx path
    .tx_pkt_start_o        (in_tx_pkt_start),
    .tx_pkt_end_i          (tx_pkt_end),
    .tx_pid_o              (in_tx_pid),
    .tx_data_avail_o       (tx_data_avail),
    .tx_data_get_i         (tx_data_get),
    .tx_data_o             (tx_data)
  );

  usb_fs_nb_out_pe #(
    .NumOutEps           (NumOutEps),
    .MaxOutPktSizeByte   (MaxPktSizeByte)
  ) u_usb_fs_nb_out_pe (
    .clk_48mhz_i            (clk_48mhz_i),
    .rst_ni                 (rst_ni),
    .link_reset_i           (link_reset_i),
    .dev_addr_i             (dev_addr_i),

    // endpoint interface
    .out_ep_current_o       (out_ep_current_o),
    .out_ep_data_put_o      (out_ep_data_put_o),
    .out_ep_put_addr_o      (out_ep_put_addr_o),
    .out_ep_data_o          (out_ep_data_o),
    .out_ep_newpkt_o        (out_ep_newpkt_o),
    .out_ep_acked_o         (out_ep_acked_o),
    .out_ep_rollback_o      (out_ep_rollback_o),
    .out_ep_setup_o         (out_ep_setup_o),
    .out_ep_full_i          (out_ep_full_i),
    .out_ep_stall_i         (out_ep_stall_i),
    .out_ep_iso_i           (out_ep_iso_i),

    .data_toggle_clear_i    (data_toggle_clear_i),

    // rx path
    .rx_pkt_start_i         (rx_pkt_start),
    .rx_pkt_end_i           (rx_pkt_end),
    .rx_pkt_valid_i         (rx_pkt_valid),
    .rx_pid_i               (rx_pid),
    .rx_addr_i              (rx_addr),
    .rx_endp_i              (rx_endp),
    .rx_data_put_i          (rx_data_put),
    .rx_data_i              (rx_data),

    // tx path
    .tx_pkt_start_o         (out_tx_pkt_start),
    .tx_pkt_end_i           (tx_pkt_end),
    .tx_pid_o               (out_tx_pid)
  );

  usb_fs_rx u_usb_fs_rx (
    .clk_i                  (clk_48mhz_i),
    .rst_ni                 (rst_ni),
    .link_reset_i           (link_reset_i),
    .cfg_eop_single_bit_i   (cfg_eop_single_bit_i),
    .cfg_rx_differential_i  (cfg_rx_differential_i),
    .usb_d_i                (usb_d_i),
    .usb_dp_i               (usb_dp_i),
    .usb_dn_i               (usb_dn_i),
    .tx_en_i                (usb_oe),
    .bit_strobe_o           (bit_strobe),
    .pkt_start_o            (rx_pkt_start),
    .pkt_end_o              (rx_pkt_end),
    .pid_o                  (rx_pid),
    .addr_o                 (rx_addr),
    .endp_o                 (rx_endp),
    .frame_num_o            (rx_frame_num),
    .rx_data_put_o          (rx_data_put),
    .rx_data_o              (rx_data),
    .valid_packet_o         (rx_pkt_valid),
    .rx_jjj_det_o           (rx_jjj_det_o),
    .crc_error_o            (rx_crc_err_o),
    .pid_error_o            (rx_pid_err_o),
    .bitstuff_error_o       (rx_bitstuff_err_o)
  );

  usb_fs_tx_mux u_usb_fs_tx_mux (
    // interface to IN Protocol Engine
    .in_tx_pkt_start_i  (in_tx_pkt_start),
    .in_tx_pid_i        (in_tx_pid),

    // interface to OUT Protocol Engine
    .out_tx_pkt_start_i (out_tx_pkt_start),
    .out_tx_pid_i       (out_tx_pid),

    // interface to tx module
    .tx_pkt_start_o     (tx_pkt_start),
    .tx_pid_o           (tx_pid)
  );

  usb_fs_tx u_usb_fs_tx (
    .clk_i                  (clk_48mhz_i),
    .rst_ni                 (rst_ni),
    .link_reset_i           (link_reset_i),
    .tx_osc_test_mode_i     (tx_osc_test_mode_i),
    .bit_strobe_i           (bit_strobe),
    .usb_d_o                (usb_d_o),
    .usb_se0_o              (usb_se0_o),
    .usb_oe_o               (usb_oe),
    .pkt_start_i            (tx_pkt_start),
    .pkt_end_o              (tx_pkt_end),
    .pid_i                  (tx_pid),
    .tx_data_avail_i        (tx_data_avail),
    .tx_data_get_o          (tx_data_get),
    .tx_data_i              (tx_data)
  );
endmodule
