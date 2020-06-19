// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: USB uart interface in USB clock domain
//
module usbuart_usbif (
  input               clk_48mhz_i,
  input               rst_ni,

  // USB lines.  Split into input vs. output and oe control signal to maintain
  // highest level of compatibility with synthesis tools.
  input  logic        usb_d_i,
  input  logic        usb_se0_i,

  output logic        usb_d_o,
  output logic        usb_se0_o,
  output logic        usb_oe_o,

  // Fifo used to communicate with system
  input               tx_empty,
  input               rx_full,
  output              tx_read,
  output              rx_write,
  output              rx_err, // Also becomes bit 8 to the fifo
  output [7:0]        rx_fifo_wdata,
  input [7:0]         tx_fifo_rdata,

  // Status
  output logic [10:0] status_frame_o,
  output logic        status_host_lost_o,
  output logic        status_host_timeout_o,
  output logic [6:0]  status_device_address_o,
  output logic [1:0]  parity_o,
  output logic [15:0] baud_o
);

  localparam int unsigned MaxPktSizeByte = 32;
  localparam int unsigned PktW = $clog2(MaxPktSizeByte);
  localparam int unsigned CtrlEp = 0;
  localparam int unsigned FifoEp = 1;

  // us_tick ticks for one cycle every us
  logic [5:0]   ns_cnt;
  logic         us_tick;
  assign us_tick = (ns_cnt == 6'd48);
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ns_cnt <= '0;
    end  else if (us_tick) begin
      ns_cnt <= '0;
    end else begin
      ns_cnt <= ns_cnt + 1'b1;
    end
  end

  logic [6:0] dev_addr;
  logic [7:0] out_ep_data;

  logic [3:0] in_ep_current;
  logic       in_ep_rollback;
  logic       in_ep_acked;
  logic [PktW - 1:0] in_ep_get_addr;
  logic               in_ep_data_get;

  logic [3:0]         out_ep_current;
  logic               out_ep_rollback;
  logic               out_ep_acked;
  logic [PktW - 1:0]  out_ep_put_addr;
  logic               out_ep_data_put;

  logic ctrl_out_ep_setup;
  logic ctrl_out_ep_stall;
  logic ctrl_out_ep_full;

  logic [7:0] ctrl_in_ep_data;
  logic ctrl_in_ep_data_done;
  logic ctrl_in_ep_stall;
  logic ctrl_in_ep_has_data;

  logic serial_out_ep_setup;
  logic serial_out_ep_stall;
  logic serial_out_ep_full;

  logic [7:0] serial_in_ep_data;
  logic serial_in_ep_data_done;
  logic serial_in_ep_stall;
  logic serial_in_ep_has_data;

  logic sof_valid;
  logic [10:0] frame_index_raw;

  logic [19:0]  host_presence_timer;

  assign status_device_address_o = dev_addr;

  logic  out_ctrl_put, out_ctrl_acked, out_ctrl_rollback;
  logic  in_ctrl_get, in_ctrl_acked, in_ctrl_rollback;
  assign out_ctrl_put      = out_ep_data_put && (out_ep_current == CtrlEp);
  assign out_ctrl_acked    = out_ep_acked    && (out_ep_current == CtrlEp);
  assign out_ctrl_rollback = out_ep_rollback && (out_ep_current == CtrlEp);
  assign in_ctrl_get       = in_ep_data_get  && (in_ep_current  == CtrlEp);
  assign in_ctrl_acked     = in_ep_acked     && (in_ep_current  == CtrlEp);
  assign in_ctrl_rollback  = in_ep_rollback  && (in_ep_current  == CtrlEp);

  usb_serial_ctrl_ep #(
    .MaxPktSizeByte(MaxPktSizeByte)
  ) u_usb_serial_ctrl_ep (
    .clk_i(clk_48mhz_i),
    .rst_ni(rst_ni),
    .dev_addr(dev_addr),

    // out endpoint interface
    .out_ep_data_put_i(out_ctrl_put),
    .out_ep_put_addr_i(out_ep_put_addr),
    .out_ep_data_i(out_ep_data),
    .out_ep_acked_i(out_ctrl_acked),
    .out_ep_rollback_i(out_ctrl_rollback),
    .out_ep_setup_i(ctrl_out_ep_setup),
    .out_ep_full_o(ctrl_out_ep_full),
    .out_ep_stall_o(ctrl_out_ep_stall),

    // in endpoint interface
    .in_ep_rollback_i(in_ctrl_rollback),
    .in_ep_acked_i(in_ctrl_acked),
    .in_ep_get_addr_i(in_ep_get_addr),
    .in_ep_data_get_i(in_ctrl_get),
    .in_ep_stall_o(ctrl_in_ep_stall),
    .in_ep_has_data_o(ctrl_in_ep_has_data),
    .in_ep_data_o(ctrl_in_ep_data[7:0]),
    .in_ep_data_done_o(ctrl_in_ep_data_done)
  );

  logic  out_fifo_put, out_fifo_acked, out_fifo_rollback;
  logic  in_fifo_get, in_fifo_acked, in_fifo_rollback;
  assign out_fifo_put      = out_ep_data_put && (out_ep_current == FifoEp);
  assign out_fifo_acked    = out_ep_acked    && (out_ep_current == FifoEp);
  assign out_fifo_rollback = out_ep_rollback && (out_ep_current == FifoEp);
  assign in_fifo_get       = in_ep_data_get  && (in_ep_current  == FifoEp);
  assign in_fifo_acked     = in_ep_acked     && (in_ep_current  == FifoEp);
  assign in_fifo_rollback  = in_ep_rollback  && (in_ep_current  == FifoEp);

  usb_serial_fifo_ep #(
    .MaxPktSizeByte(MaxPktSizeByte)
  ) u_usb_serial_fifo_ep (
    .clk_i(clk_48mhz_i),
    .rst_ni(rst_ni),
    // out endpoint interface
    .out_ep_data_put_i(out_fifo_put),
    .out_ep_put_addr_i(out_ep_put_addr),
    .out_ep_data_i(out_ep_data),
    .out_ep_acked_i(out_fifo_acked),
    .out_ep_rollback_i(out_fifo_rollback),
    .out_ep_setup_i(serial_out_ep_setup),
    .out_ep_full_o(serial_out_ep_full),
    .out_ep_stall_o(serial_out_ep_stall),

    // in endpoint interface
    .in_ep_rollback_i(in_fifo_rollback),
    .in_ep_acked_i(in_fifo_acked),
    .in_ep_get_addr_i(in_ep_get_addr),
    .in_ep_data_get_i(in_fifo_get),
    .in_ep_stall_o(serial_in_ep_stall),
    .in_ep_has_data_o(serial_in_ep_has_data),
    .in_ep_data_o(serial_in_ep_data[7:0]),
    .in_ep_data_done_o(serial_in_ep_data_done),

    // fifo interface
    .tx_empty(tx_empty),
    .rx_full(rx_full),
    .tx_read(tx_read),
    .rx_write(rx_write),
    .rx_err(rx_err), // Also becomes bit 8 to the fifo
    .rx_fifo_wdata(rx_fifo_wdata),
    .tx_fifo_rdata(tx_fifo_rdata),
    // information
    .parity_o(parity_o),
    .baud_o(baud_o)
  );

  usb_fs_nb_pe #(
    .NumOutEps(2),
    .NumInEps(2),
    .MaxPktSizeByte(MaxPktSizeByte)
  ) u_usb_fs_nb_pe (
    .clk_48mhz_i                (clk_48mhz_i),
    .rst_ni                     (rst_ni),
    .link_reset_i               (1'b0), // TODO need to reset if link resets

    // USB TRX interface (sync)
    .usb_d_i                    (usb_d_i),
    .usb_se0_i                  (usb_se0_i),
    .usb_d_o                    (usb_d_o),
    .usb_se0_o                  (usb_se0_o),
    .usb_oe_o                   (usb_oe_o),

    // Global configuration (static)
    .cfg_eop_single_bit_i       (1'b1),
    .tx_osc_test_mode_i         (1'b0),
    .data_toggle_clear_i        (2'b0),

    .dev_addr_i                 (dev_addr),

    // out endpoint interfaces
    .out_ep_current_o           (out_ep_current),
    .out_ep_data_put_o          (out_ep_data_put),
    .out_ep_put_addr_o          (out_ep_put_addr),
    .out_ep_data_o              (out_ep_data),
    .out_ep_acked_o             (out_ep_acked),
    .out_ep_rollback_o          (out_ep_rollback),
    .out_ep_newpkt_o            (),
    .out_ep_setup_o             ({serial_out_ep_setup, ctrl_out_ep_setup}),
    .out_ep_full_i              ({serial_out_ep_full, ctrl_out_ep_full}),
    .out_ep_stall_i             ({serial_out_ep_stall, ctrl_out_ep_stall}),
    .out_ep_iso_i               (2'b0),

    // in endpoint interfaces
    .in_ep_current_o            (in_ep_current),
    .in_ep_rollback_o           (in_ep_rollback),
    .in_ep_acked_o              (in_ep_acked),
    .in_ep_get_addr_o           (in_ep_get_addr),
    .in_ep_data_get_o           (in_ep_data_get),
    .in_ep_newpkt_o             (),
    .in_ep_stall_i              ({serial_in_ep_stall, ctrl_in_ep_stall}),
    .in_ep_has_data_i           ({serial_in_ep_has_data, ctrl_in_ep_has_data}),
    .in_ep_data_i               ((in_ep_current == 4'b0001) ? serial_in_ep_data : ctrl_in_ep_data),
    .in_ep_data_done_i          ({serial_in_ep_data_done, ctrl_in_ep_data_done}),
    .in_ep_iso_i                (2'b0),

    // Errors
    .rx_crc_err_o               (),
    .rx_pid_err_o               (),
    .rx_bitstuff_err_o          (),

    // sof interface
    .sof_valid_o                (sof_valid),
    .frame_index_o              (frame_index_raw)
  );

  // host presence detection
  // host_lost if no sof in 2.048ms (supposed to be every 1ms)
  // host_presence_timeout if no sof in 1s (spec)
  assign status_host_lost_o = host_presence_timer[19:12] != 0;
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      host_presence_timer <= '0;
      status_host_timeout_o <= 1'b0;
      status_frame_o <= '0;
    end else begin
      if (sof_valid) begin
        host_presence_timer <= 0;
        status_host_timeout_o <= 0;
        status_frame_o <= frame_index_raw;
      end else if (host_presence_timer > 1000000) begin
        status_host_timeout_o <= 1;
      end else if (us_tick) begin
        host_presence_timer <= host_presence_timer + 1;
      end
    end
  end
endmodule
