// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: USB uart interface in USB clock domain
//
module usbuart_usbif (
  input logic         clk_48mhz_i,
  input logic         rst_ni,

  // USB lines
  input logic         usb_d_i,
  input logic         usb_dp_i,
  input logic         usb_dn_i,

  output logic        usb_d_o,
  output logic        usb_se0_o,
  output logic        usb_oe_o,
  input logic         rx_diff_mode_i,

  // SOF reference for clock calibration
  input logic         usb_ref_disable_i,
  output logic        usb_ref_val_o,
  output logic        usb_ref_pulse_o,

  // Fifo used to communicate with system
  input logic         tx_empty,
  input logic         rx_full,
  output logic        tx_read,
  output logic        rx_write,
  output logic        rx_err, // Also becomes bit 8 to the fifo
  output logic [7:0]  rx_fifo_wdata,
  input logic [7:0]   tx_fifo_rdata,

  // Status
  output logic [10:0] frame_o,
  output logic        host_lost_o,
  output logic        link_reset_o,
  output logic        link_suspend_o,
  output logic [6:0]  device_address_o,
  output logic [1:0]  parity_o,
  output logic [15:0] baud_o
);

  localparam int unsigned MaxPktSizeByte = 32;
  localparam int unsigned PktW = $clog2(MaxPktSizeByte);
  localparam bit [3:0]    CtrlEp = 4'd0;
  localparam bit [3:0]    FifoEp = 4'd1;

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
  logic see_js;

  assign device_address_o = dev_addr;

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
    .link_reset_i(link_reset_o),
    .dev_addr_o(dev_addr),

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
    .tx_empty_i(tx_empty),
    .rx_full_i(rx_full),
    .tx_read_o(tx_read),
    .rx_write_o(rx_write),
    .rx_err_o(rx_err), // Also becomes bit 8 to the fifo
    .rx_fifo_wdata_o(rx_fifo_wdata),
    .tx_fifo_rdata_i(tx_fifo_rdata),
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
    .link_reset_i               (link_reset_o),
    .dev_addr_i                 (dev_addr),

    // Global configuration (static)
    .cfg_eop_single_bit_i       (1'b1),
    .cfg_rx_differential_i      (rx_diff_mode_i),
    .tx_osc_test_mode_i         (1'b0),
    .data_toggle_clear_i        (2'b0),

    // out endpoint interfaces
    .out_ep_current_o           (out_ep_current),
    .out_ep_data_put_o          (out_ep_data_put),
    .out_ep_put_addr_o          (out_ep_put_addr),
    .out_ep_data_o              (out_ep_data),
    .out_ep_newpkt_o            (),
    .out_ep_acked_o             (out_ep_acked),
    .out_ep_rollback_o          (out_ep_rollback),
    .out_ep_setup_o             ({serial_out_ep_setup, ctrl_out_ep_setup}),
    .out_ep_full_i              ({serial_out_ep_full, ctrl_out_ep_full}),
    .out_ep_stall_i             ({serial_out_ep_stall, ctrl_out_ep_stall}),
    .out_ep_iso_i               (2'b0),

    // in endpoint interfaces
    .in_ep_current_o            (in_ep_current),
    .in_ep_rollback_o           (in_ep_rollback),
    .in_ep_xfr_end_o            (),             // using this has logic loop because of iso case
    .in_ep_acked_o              (in_ep_acked),  // must get ack
    .in_ep_get_addr_o           (in_ep_get_addr),
    .in_ep_data_get_o           (in_ep_data_get),
    .in_ep_newpkt_o             (),
    .in_ep_stall_i              ({serial_in_ep_stall, ctrl_in_ep_stall}),
    .in_ep_has_data_i           ({serial_in_ep_has_data, ctrl_in_ep_has_data}),
    .in_ep_data_i               ((in_ep_current == 4'b0001) ? serial_in_ep_data : ctrl_in_ep_data),
    .in_ep_data_done_i          ({serial_in_ep_data_done, ctrl_in_ep_data_done}),
    .in_ep_iso_i                (2'b0),

    // sof interface
    .sof_valid_o                (sof_valid),
    .frame_index_o              (frame_index_raw),
    // RX line status
    .rx_jjj_det_o               (see_js),

    // Errors
    .rx_crc_err_o (),
    .rx_pid_err_o (),
    .rx_bitstuff_err_o (),

    // USB TRX interface (sync)
    .usb_d_i                    (usb_d_i),
    .usb_dp_i                   (usb_dp_i),
    .usb_dn_i                   (usb_dn_i),
    .usb_d_o                    (usb_d_o),
    .usb_se0_o                  (usb_se0_o),
    .usb_oe_o                   (usb_oe_o)
  );


  // Simple detection of reset, suspend and lack of SOF
  // Lack of SOF for 4.096ms will cause a break condition to be reported

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



  // suspend must be detected if line is J for 3ms
  logic [12:0] sus_timer_us;

  assign link_suspend_o = sus_timer_us > 3000; // 3000us == 3ms

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sus_timer_us <= '0;
    end else begin
      if (!see_js) begin
        sus_timer_us <= '0;
      end else if (us_tick && !link_suspend_o) begin
        sus_timer_us <= sus_timer_us + 1;
      end
    end
  end

  // reset detected if line is SE0 for >=2.5us, but host must hold at least 10ms
  // This will detect in 3-4us depending if the reset started immediately before (3us)
  // or immediately after (4us) a us_tick pulse
  logic [2:0] res_timer_us;
  logic       see_se0;

  assign link_reset_o = res_timer_us[2];
  assign see_se0 = (usb_dp_i == 0) && (usb_dn_i == 0);

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      res_timer_us <= '0;
    end else begin
      if (!see_se0) begin
        res_timer_us <= '0;
      end else if (us_tick && !link_reset_o) begin
        res_timer_us <= res_timer_us + 1;
      end
    end
  end

  // host_lost if no sof in 4.096ms (supposed to be every 1ms)
  // (don't take account of link state so this will trigger for suspend and reset)
  logic [12:0] no_sof_timer_us;

  assign host_lost_o = no_sof_timer_us[12];
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      no_sof_timer_us <= '0;
    end else begin
      if (sof_valid) begin  // removed  || link_suspend_o || link_reset_o
        no_sof_timer_us <= '0;
      end else if (us_tick && !host_lost_o) begin
        no_sof_timer_us <= no_sof_timer_us + 1;
      end
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      frame_o <= '0;
    end else begin
      if (sof_valid) begin
        frame_o <= frame_index_raw;
      end
    end
  end

  /////////////////////////////////////////
  // SOF Reference for Clock Calibration //
  /////////////////////////////////////////

  logic usb_ref_val_d, usb_ref_val_q;

  // Directly forward the pulse unless disabled.
  assign usb_ref_pulse_o = usb_ref_disable_i ? 1'b0 : sof_valid;

  // The first pulse is always ignored, but causes the valid to be asserted.
  // The valid signal is deasserted when:
  // - The link is no longer active. TODO
  // - The host is lost (no SOF for 4ms).
  // - The reference generation is disabled.
  assign usb_ref_val_d = usb_ref_pulse_o                           ? 1'b1 :
    (host_lost_o || link_reset_o || link_suspend_o || usb_ref_disable_i) ? 1'b0 : usb_ref_val_q;

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      usb_ref_val_q <= 1'b0;
    end else begin
      usb_ref_val_q <= usb_ref_val_d;
    end
  end

  assign usb_ref_val_o = usb_ref_val_q;


endmodule
