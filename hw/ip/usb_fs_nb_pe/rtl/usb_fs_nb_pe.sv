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
  parameter NumOutEps = 2,
  parameter NumInEps = 2,
  parameter MaxPktSizeByte = 32,
  parameter PktW = $clog2(MaxPktSizeByte)
) (
  input                          clk_48mhz_i,
  input                          rst_ni,
  input                          link_reset_i, // synchronous with clk_48mhz_i
  input [6:0]                    dev_addr_i,

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
  input [NumOutEps-1:0]          out_ep_full_i, // Cannot accept data
  input [NumOutEps-1:0]          out_ep_stall_i, // Stalled

  // in endpoint interfaces
  output logic [3:0]             in_ep_current_o, // Other signals addressed to this ep
  output logic                   in_ep_rollback_o, // Bad termination, rollback transaction
  output logic                   in_ep_acked_o, // good termination, transaction complete
  output logic [PktW - 1:0]      in_ep_get_addr_o, // Offset requested (0..pktlen)
  output logic                   in_ep_data_get_o, // Accept data (get_addr advances too)
  output logic                   in_ep_newpkt_o, // New IN pkt start (with in_ep_current_o update)
  input [NumInEps-1:0]           in_ep_stall_i, // Endpoint in a stall state
  input [NumInEps-1:0]           in_ep_has_data_i, // Endpoint has data to supply
  input [7:0]                    in_ep_data_i, // Data for current get_addr
  input [NumInEps-1:0]           in_ep_data_done_i, // Set when out of data

  // sof interface
  output                         sof_valid_o,
  output [10:0]                  frame_index_o,

  /////////////////////////
  // USB TX/RX Interface //
  /////////////////////////
  output                         usb_p_tx_o,
  output                         usb_n_tx_o,

  input                          usb_p_rx_i,
  input                          usb_n_rx_i,

  output                         usb_tx_en_o
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

  // sof interface
  assign sof_valid_o = rx_pkt_end && rx_pkt_valid && (usb_pid_e'(rx_pid) == UsbPidSof);
  assign frame_index_o = rx_frame_num;

  usb_fs_nb_in_pe #(
    .NumInEps(NumInEps),
    .MaxInPktSizeByte(MaxPktSizeByte)
  ) u_usb_fs_nb_in_pe (
    .clk_48mhz_i(clk_48mhz_i),
    .rst_ni(rst_ni),
    .link_reset_i(link_reset_i),
    .dev_addr_i(dev_addr_i),

    // endpoint interface
    .in_ep_current_o(in_ep_current_o),
    .in_ep_rollback_o(in_ep_rollback_o),
    .in_ep_acked_o(in_ep_acked_o),
    .in_ep_get_addr_o(in_ep_get_addr_o),
    .in_ep_data_get_o(in_ep_data_get_o),
    .in_ep_newpkt_o(in_ep_newpkt_o),
    .in_ep_stall_i(in_ep_stall_i),
    .in_ep_has_data_i(in_ep_has_data_i),
    .in_ep_data_i(in_ep_data_i),
    .in_ep_data_done_i(in_ep_data_done_i),

    // rx path
    .rx_pkt_start_i(rx_pkt_start),
    .rx_pkt_end_i(rx_pkt_end),
    .rx_pkt_valid_i(rx_pkt_valid),
    .rx_pid_i(rx_pid),
    .rx_addr_i(rx_addr),
    .rx_endp_i(rx_endp),

    // tx path
    .tx_pkt_start_o(in_tx_pkt_start),
    .tx_pkt_end_i(tx_pkt_end),
    .tx_pid_o(in_tx_pid),
    .tx_data_avail_o(tx_data_avail),
    .tx_data_get_i(tx_data_get),
    .tx_data_o(tx_data)
  );

  usb_fs_nb_out_pe #(
    .NumOutEps(NumOutEps),
    .MaxOutPktSizeByte(MaxPktSizeByte)
  ) u_usb_fs_nb_out_pe (
    .clk_48mhz_i(clk_48mhz_i),
    .rst_ni(rst_ni),
    .link_reset_i(link_reset_i),
    .dev_addr_i(dev_addr_i),

    // endpoint interface
    .out_ep_current_o(out_ep_current_o),
    .out_ep_data_put_o(out_ep_data_put_o),
    .out_ep_put_addr_o(out_ep_put_addr_o),
    .out_ep_data_o(out_ep_data_o),
    .out_ep_newpkt_o(out_ep_newpkt_o),
    .out_ep_acked_o(out_ep_acked_o),
    .out_ep_rollback_o(out_ep_rollback_o),
    .out_ep_setup_o(out_ep_setup_o),
    .out_ep_full_i(out_ep_full_i),
    .out_ep_stall_i(out_ep_stall_i),

    // rx path
    .rx_pkt_start_i(rx_pkt_start),
    .rx_pkt_end_i(rx_pkt_end),
    .rx_pkt_valid_i(rx_pkt_valid),
    .rx_pid_i(rx_pid),
    .rx_addr_i(rx_addr),
    .rx_endp_i(rx_endp),
    .rx_data_put_i(rx_data_put),
    .rx_data_i(rx_data),

    // tx path
    .tx_pkt_start_o(out_tx_pkt_start),
    .tx_pkt_end_i(tx_pkt_end),
    .tx_pid_o(out_tx_pid)
  );

  usb_fs_rx u_usb_fs_rx (
    .clk_48mhz(clk_48mhz_i),
    .reset(link_reset_i),
    .dp(usb_p_rx_i),
    .dn(usb_n_rx_i),
    .bit_strobe(bit_strobe),
    .pkt_start(rx_pkt_start),
    .pkt_end(rx_pkt_end),
    .pid(rx_pid),
    .addr(rx_addr),
    .endp(rx_endp),
    .frame_num(rx_frame_num),
    .rx_data_put(rx_data_put),
    .rx_data(rx_data),
    .valid_packet(rx_pkt_valid)
  );

  usb_fs_tx_mux u_usb_fs_tx_mux (
    // interface to IN Protocol Engine
    .in_tx_pkt_start(in_tx_pkt_start),
    .in_tx_pid(in_tx_pid),

    // interface to OUT Protocol Engine
    .out_tx_pkt_start(out_tx_pkt_start),
    .out_tx_pid(out_tx_pid),

    // interface to tx module
    .tx_pkt_start(tx_pkt_start),
    .tx_pid(tx_pid)
  );

  usb_fs_tx u_usb_fs_tx (
    .clk_48mhz(clk_48mhz_i),
    .reset(link_reset_i),
    .bit_strobe(bit_strobe),
    .oe(usb_tx_en_o),
    .dp(usb_p_tx_o),
    .dn(usb_n_tx_o),
    .pkt_start(tx_pkt_start),
    .pkt_end(tx_pkt_end),
    .pid(tx_pid),
    .tx_data_avail(tx_data_avail),
    .tx_data_get(tx_data_get),
    .tx_data(tx_data)
  );
endmodule
