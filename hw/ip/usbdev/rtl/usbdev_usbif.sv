// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB Full-Speed Device Interface core internals
//
//

`include "prim_assert.sv"

// This module runs on the 48MHz USB clock
module usbdev_usbif  #(
  parameter int NEndpoints = 12,
  parameter int AVFifoWidth = 4,
  parameter int RXFifoWidth = 4,
  parameter int MaxPktSizeByte = 64,
  parameter int NBuf = 4,
  parameter int SramAw = 4,
  localparam int NBufWidth = $clog2(NBuf), // derived parameter
  localparam int PktW = $clog2(MaxPktSizeByte) // derived parameter
) (
  input  logic                     clk_48mhz_i, // 48MHz USB clock
  input  logic                     rst_ni,

  // Pins (synchronous)
  input  logic                     usb_d_i,
  input  logic                     usb_dp_i,
  input  logic                     usb_dn_i,

  output logic                     usb_d_o,
  output logic                     usb_se0_o,
  output logic                     usb_dp_o,
  output logic                     usb_dn_o,
  output logic                     usb_oe_o,

  output logic                     usb_pullup_en_o,
  input  logic                     usb_sense_i,

  // receive (OUT or SETUP) side
  input  logic [NEndpoints-1:0]    rx_setup_i,
  input  logic [NEndpoints-1:0]    rx_out_i,
  input  logic [NEndpoints-1:0]    rx_stall_i,
  input  logic                     avsetup_rvalid_i,
  output logic                     avsetup_rready_o,
  input  logic [AVFifoWidth - 1: 0]avsetup_rdata_i,
  input  logic                     avout_rvalid_i,
  output logic                     avout_rready_o,
  input  logic [AVFifoWidth - 1: 0]avout_rdata_i,

  output logic                     rx_wvalid_o,
  input  logic                     rx_wready_setup_i,
  input  logic                     rx_wready_out_i,
  output logic [RXFifoWidth - 1:0] rx_wdata_o,
  output logic                     setup_received_o,
  output logic [3:0]               out_endpoint_o,
  output logic                     out_endpoint_val_o,

  // transmit (IN) side
  output logic                     in_xact_starting_o,
  output logic [3:0]               in_xact_start_ep_o,
  input  logic [NBufWidth - 1:0]   in_buf_i,
  input  logic [PktW:0]            in_size_i,
  input  logic [NEndpoints-1:0]    in_stall_i,
  input  logic [NEndpoints-1:0]    in_rdy_i,
  output logic                     in_ep_xact_end_o,
  output logic [3:0]               in_endpoint_o,
  output logic                     in_endpoint_val_o,

  // memory interface
  output logic                     mem_req_o,
  output logic                     mem_write_o,
  output logic [SramAw-1:0]        mem_addr_o,
  output logic [31:0]              mem_wdata_o,
  input  logic [31:0]              mem_rdata_i,

  // time reference
  input  logic                     us_tick_i,

  // control
  input  logic                     connect_en_i,
  input  logic [6:0]               devaddr_i,
  output logic                     clr_devaddr_o,
  input  logic [NEndpoints-1:0]    in_ep_enabled_i,
  input  logic [NEndpoints-1:0]    out_ep_enabled_i,
  input  logic [NEndpoints-1:0]    out_ep_iso_i,
  input  logic [NEndpoints-1:0]    in_ep_iso_i,
  input  logic                     diff_rx_ok_i, // 1: differential symbols (K/J) are valid
  input  logic                     cfg_eop_single_bit_i, // 1: detect a single SE0 bit as EOP
  input  logic                     cfg_use_diff_rcvr_i, // 1: use single-ended rx data on usb_d_i
  input  logic                     cfg_pinflip_i, // 1: Treat outputs and inputs as though D+/D-
                                                  // are flipped
  input  logic                     tx_osc_test_mode_i, // Oscillator test mode: constant JK output
  output logic [NEndpoints-1:0]    out_data_toggle_o, // Current state of OUT data toggles
  input  logic                     out_datatog_we_i, // OUT data toggles write strobe from software
  input  logic [NEndpoints-1:0]    out_datatog_status_i, // New state of selected OUT data toggles
  input  logic [NEndpoints-1:0]    out_datatog_mask_i, // Which OUT EP data toggles to modify
  output logic [NEndpoints-1:0]    in_data_toggle_o, // Current state of IN data toggles
  input  logic                     in_datatog_we_i, // IN data toggles write strobe from software
  input  logic [NEndpoints-1:0]    in_datatog_status_i, // New state of selected IN data toggles
  input  logic [NEndpoints-1:0]    in_datatog_mask_i, // Which IN EP data toggles to modify
  input  logic                     resume_link_active_i, // Jump from LinkPowered to LinkResuming

  // status
  output logic                     frame_start_o, // Pulses with host-generated and internal SOF
  output logic [10:0]              frame_o,
  output logic                     sof_detected_o, // Pulses with only host-generated SOF.
                                                   // Used for clock sync.
  output logic [2:0]               link_state_o,
  output logic                     link_disconnect_o,
  output logic                     link_powered_o,
  output logic                     link_reset_o,
  output logic                     link_active_o,
  output logic                     link_suspend_o,
  output logic                     link_resume_o,
  output logic                     link_in_err_o,
  output logic                     link_out_err_o,
  output logic                     host_lost_o,
  output logic                     rx_crc5_err_o,
  output logic                     rx_crc16_err_o,
  output logic                     rx_pid_err_o,
  output logic                     rx_bitstuff_err_o,

  // event counters
  output logic                     event_ign_avsetup_o,
  output logic                     event_drop_avout_o,
  output logic                     event_drop_rx_o,
  output logic                     event_datatog_out_o,
  output logic                     event_timeout_in_o,
  output logic                     event_nak_in_o,
  output logic                     event_nodata_in_o
);

  // Enable pull-up resistor only if VBUS is active
  assign usb_pullup_en_o = connect_en_i & usb_sense_i;

  // OUT or SETUP direction
  logic [PktW:0]                     out_max_used_d, out_max_used_q;
  logic [PktW-1:0]                   out_ep_put_addr;
  logic [7:0]                        out_ep_data;

  logic [3:0]                        out_ep_current;
  logic                              out_ep_newpkt, out_ep_data_put, out_ep_acked, out_ep_rollback;
  logic                              current_setup, all_out_blocked;
  logic [NEndpoints-1:0]             out_ep_setup, out_ep_full, out_ep_stall;
  logic [NEndpoints-1:0]             out_blocked;
  logic [31:0]                       wdata_q, wdata_d;
  logic                              mem_read;
  logic [SramAw-1:0]                 mem_waddr, mem_raddr;
  logic                              link_reset;

  // Make sure out_endpoint_o can safely be used to index signals of NEndpoints width.
  assign out_endpoint_val_o = int'(out_ep_current) < NEndpoints;
  assign out_endpoint_o     = out_endpoint_val_o ? out_ep_current : '0;

  assign link_reset_o   = link_reset;
  assign clr_devaddr_o  = ~connect_en_i | link_reset;
  assign link_out_err_o = out_ep_rollback;

  always_comb begin
    if (out_ep_acked || out_ep_rollback) begin
      out_max_used_d = 0;

    end else if (out_ep_data_put) begin
      // In the normal case <MaxPktSizeByte this is out_max_used_q <= out_ep_put_addr
      // Following all ones out_max_used_q will get 1,00..00 and 1,00..01 to cover
      // one and two bytes of the CRC overflowing, then stick at 1,00..01
      if (int'(out_max_used_q) < MaxPktSizeByte - 1) begin
        out_max_used_d = {1'b0, out_ep_put_addr};
      end else if (int'(out_max_used_q) < MaxPktSizeByte + 1) begin
        out_max_used_d = out_max_used_q + 1;
      end else begin
        out_max_used_d = out_max_used_q;
      end

    end else begin
      out_max_used_d = out_max_used_q;
    end
  end // always_comb

  // don't write if the address has wrapped (happens for two CRC bytes after max data)
  logic std_write_d, std_write_q;
  assign std_write_d = out_ep_data_put & ((int'(out_max_used_q) < MaxPktSizeByte - 1) &
      (out_ep_put_addr[1:0] == 2'b11));

  always_comb begin
    wdata_d = wdata_q;

    unique case (out_ep_put_addr[1:0])
      0:       wdata_d[7:0]   = out_ep_data;
      1:       wdata_d[15:8]  = out_ep_data;
      2:       wdata_d[23:16] = out_ep_data;
      3:       wdata_d[31:24] = out_ep_data;
      default: wdata_d[7:0]   = out_ep_data;
    endcase
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_max_used_q <= '0;
      wdata_q        <= '0;
      std_write_q    <= 1'b0;
    end else if (link_reset) begin
      out_max_used_q <= '0;
      std_write_q    <= 1'b0;
    end else begin
      out_max_used_q <= out_max_used_d;
      std_write_q    <= std_write_d;

      if (out_ep_data_put) begin
        wdata_q <= wdata_d;
      end
    end
  end // always_ff @ (posedge clk_48mhz_i)

  // select from the appropriate Available Buffer FIFO, SETUP or OUT.
  logic av_rvalid;
  logic [AVFifoWidth-1:0] av_rdata;
  assign av_rvalid = current_setup ? avsetup_rvalid_i : avout_rvalid_i;
  assign av_rdata  = current_setup ? avsetup_rdata_i  : avout_rdata_i;

  // only SETUP packets are permitted to fill the RxFIFO completely, ensuring that we can always
  // receive a SETUP packet even under heavy OUT traffic and high software latency.
  logic rx_wready;
  assign rx_wready = current_setup ? rx_wready_setup_i : rx_wready_out_i;

  // need extra write at end if packet not multiple of 4 bytes
  assign mem_write_o = av_rvalid & (std_write_q |
                       (~out_max_used_q[PktW] & (out_max_used_q[1:0] != 2'b11) & out_ep_acked));
  assign mem_waddr = {av_rdata, out_max_used_q[PktW-1:2]};
  assign mem_wdata_o = wdata_q;
  assign mem_addr_o = mem_write_o ? mem_waddr : mem_raddr;
  assign mem_req_o = mem_read | mem_write_o;
  // Is the DATA packet currently being received a SETUP DATA packet or a regular OUT DATA packet?
  assign current_setup = out_ep_setup[out_endpoint_o];

  logic [PktW:0] out_max_minus1;
  // -2 for CRC bytes but +1 for zero-based address to size
  assign out_max_minus1 = out_max_used_q - 1;

  assign rx_wdata_o = {
      out_endpoint_o,
      current_setup,
      out_max_minus1,
      av_rdata
  };
  assign rx_wvalid_o = out_ep_acked;
  // Pop the available fifo after the write that used the previous value
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      avsetup_rready_o <= 1'b0;
      avout_rready_o   <= 1'b0;
    end else begin
      avsetup_rready_o <= rx_wvalid_o &  current_setup;
      avout_rready_o   <= rx_wvalid_o & ~current_setup;
    end
  end

  // full here covers the software blocking by clearing the enable
  assign out_blocked = ~out_ep_setup & ~rx_out_i;
  // full also covers being blocked because the hardware can't take any transactions at all
  assign all_out_blocked = (~rx_wready) | (~av_rvalid);

  assign out_ep_full = {NEndpoints{all_out_blocked}} | out_blocked;
  assign out_ep_stall = rx_stall_i;

  // Need to clear IN read if a SETUP is received because it may use the IN channel
  // This will not trigger, if the AV Buffer is empty, in that case we have replied
  // with a NAK, which is illegal anyway
  assign setup_received_o = current_setup & rx_wvalid_o;

  // IN (device to host) transactions
  logic                  in_ep_data_get, in_data_done, in_ep_newpkt, pkt_start_rd;
  logic [NEndpoints-1:0] in_ep_data_done;
  logic [PktW-1:0]       in_ep_get_addr;
  logic [7:0]            in_ep_data;
  logic [3:0]            in_ep_current;

  // Make sure in_endpoint_o can safely be used to index signals of NEndpoints width.
  assign in_endpoint_val_o = int'(in_ep_current) < NEndpoints;
  assign in_endpoint_o     = in_endpoint_val_o ? in_ep_current : '0;

  // The protocol engine will automatically generate done for a full-length packet
  // Note: this does the correct thing for sending zero length packets
  assign in_data_done = {1'b0, in_ep_get_addr} == in_size_i;
  always_comb begin
    in_ep_data_done = '0;
    in_ep_data_done[in_endpoint_o] = in_data_done;
  end

  // Need extra read at start of packet to get the first word of data
  // Delay by one cycle from the in_endpoint update
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pkt_start_rd <= 1'b0;
    end else begin
      pkt_start_rd <= in_ep_newpkt;
    end
  end

  assign mem_raddr = {in_buf_i,in_ep_get_addr[PktW-1:2]};
  assign mem_read = pkt_start_rd | (in_ep_data_get & (in_ep_get_addr[1:0] == 2'b0));

  assign in_ep_data = in_ep_get_addr[1] ?
                      (in_ep_get_addr[0] ? mem_rdata_i[31:24] : mem_rdata_i[23:16]) :
                      (in_ep_get_addr[0] ? mem_rdata_i[15:8]  : mem_rdata_i[7:0]);

  logic            sof_valid;
  logic [10:0]     frame_index_raw;
  logic            rx_idle_det;
  logic            rx_j_det;

  usb_fs_nb_pe #(
    .NumOutEps      (NEndpoints),
    .NumInEps       (NEndpoints),
    .MaxPktSizeByte (MaxPktSizeByte)
  ) u_usb_fs_nb_pe (
    .clk_48mhz_i           (clk_48mhz_i),
    .rst_ni                (rst_ni),
    .link_reset_i          (link_reset),
    .link_active_i         (link_active_o),

    .cfg_eop_single_bit_i  (cfg_eop_single_bit_i),
    .cfg_use_diff_rcvr_i   (cfg_use_diff_rcvr_i),
    .cfg_pinflip_i         (cfg_pinflip_i),
    .tx_osc_test_mode_i    (tx_osc_test_mode_i),
    .out_data_toggle_o     (out_data_toggle_o),
    .out_datatog_we_i      (out_datatog_we_i),
    .out_datatog_status_i  (out_datatog_status_i),
    .out_datatog_mask_i    (out_datatog_mask_i),
    .in_data_toggle_o      (in_data_toggle_o),
    .in_datatog_we_i       (in_datatog_we_i),
    .in_datatog_status_i   (in_datatog_status_i),
    .in_datatog_mask_i     (in_datatog_mask_i),
    .diff_rx_ok_i          (diff_rx_ok_i),

    .usb_d_i               (usb_d_i),
    .usb_dp_i              (usb_dp_i),
    .usb_dn_i              (usb_dn_i),
    .usb_d_o               (usb_d_o),
    .usb_se0_o             (usb_se0_o),
    .usb_dp_o              (usb_dp_o),
    .usb_dn_o              (usb_dn_o),
    .usb_oe_o              (usb_oe_o),

    .dev_addr_i            (devaddr_i),

    // out endpoint interfaces
    .out_ep_current_o      (out_ep_current),
    .out_ep_newpkt_o       (out_ep_newpkt),
    .out_ep_data_put_o     (out_ep_data_put),
    .out_ep_put_addr_o     (out_ep_put_addr),
    .out_ep_data_o         (out_ep_data),
    .out_ep_acked_o        (out_ep_acked),
    .out_ep_rollback_o     (out_ep_rollback),
    .out_ep_setup_o        (out_ep_setup),
    .out_ep_enabled_i      (out_ep_enabled_i),
    .out_ep_control_i      (rx_setup_i),
    .out_ep_full_i         (out_ep_full),
    .out_ep_stall_i        (out_ep_stall),
    .out_ep_iso_i          (out_ep_iso_i),

    // in endpoint interfaces
    .in_xact_starting_o    (in_xact_starting_o),
    .in_xact_start_ep_o    (in_xact_start_ep_o),

    .in_ep_current_o       (in_ep_current),
    .in_ep_rollback_o      (link_in_err_o),
    .in_ep_xact_end_o      (in_ep_xact_end_o),
    .in_ep_get_addr_o      (in_ep_get_addr),
    .in_ep_data_get_o      (in_ep_data_get),
    .in_ep_newpkt_o        (in_ep_newpkt),
    .in_ep_enabled_i       (in_ep_enabled_i),
    .in_ep_stall_i         (in_stall_i),
    .in_ep_has_data_i      (in_rdy_i),
    .in_ep_data_i          (in_ep_data),
    .in_ep_data_done_i     (in_ep_data_done),
    .in_ep_iso_i           (in_ep_iso_i),

    // rx status
    .rx_idle_det_o         (rx_idle_det),
    .rx_j_det_o            (rx_j_det),

    // error signals
    .rx_crc5_err_o         (rx_crc5_err_o),
    .rx_crc16_err_o        (rx_crc16_err_o),
    .rx_pid_err_o          (rx_pid_err_o),
    .rx_bitstuff_err_o     (rx_bitstuff_err_o),

    // sof interface
    .sof_detected_o        (sof_detected_o),
    .sof_valid_o           (sof_valid),
    .frame_index_o         (frame_index_raw),

    // event counters
    .event_datatog_out_o   (event_datatog_out_o),
    .event_timeout_in_o    (event_timeout_in_o),
    .event_nak_in_o        (event_nak_in_o),
    .event_nodata_in_o     (event_nodata_in_o)
  );

  // Capture frame number (host sends every 1ms)
  // Generate an internal SOF if the host's is missing.
  logic do_internal_sof;
  logic [10:0] frame_d, frame_q;

  assign frame_o = frame_q;
  assign frame_start_o = (frame_q != frame_d);

  always_comb begin
    frame_d = frame_q;
    if (sof_valid) begin
      frame_d = frame_index_raw;
    end else if (sof_detected_o | do_internal_sof) begin
      frame_d = frame_q + 1;
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      frame_q <= '0;
    end else begin
      frame_q <= frame_d;
    end
  end

  usbdev_linkstate u_usbdev_linkstate (
    .clk_48mhz_i           (clk_48mhz_i),
    .rst_ni                (rst_ni),
    .us_tick_i             (us_tick_i),
    .usb_sense_i           (usb_sense_i),
    .usb_dp_i              (usb_dp_i),
    .usb_dn_i              (usb_dn_i),
    .usb_oe_i              (usb_oe_o),
    .usb_pullup_en_i       (connect_en_i),
    .rx_idle_det_i         (rx_idle_det),
    .rx_j_det_i            (rx_j_det),
    .sof_detected_i        (sof_detected_o),
    .resume_link_active_i  (resume_link_active_i),
    .link_disconnect_o     (link_disconnect_o),
    .link_powered_o        (link_powered_o),
    .link_reset_o          (link_reset),
    .link_active_o         (link_active_o),
    .link_suspend_o        (link_suspend_o),
    .link_resume_o         (link_resume_o),
    .link_state_o          (link_state_o),
    .host_lost_o           (host_lost_o),
    .sof_missed_o          (do_internal_sof)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////
  // Count the number of SETUP and OUT packets ignored because there is no available buffer in
  // the appropriate FIFO, and the number of SETUP/OUT packets dropped because the RX FIFO
  // will not accept another buffer.
  //////////////////////////////////////////////////////////////////////////////////////////////
  logic ign_avsetup;
  logic drop_avout;
  logic drop_rx;
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ign_avsetup <= 1'b0;
      drop_avout  <= 1'b0;
      drop_rx     <= 1'b0;
    end else begin
      // Ignore SETUP packets because no Available SETUP Buffer
      if (out_ep_newpkt) ign_avsetup <= 1'b0;
      else if (out_ep_data_put & current_setup & !avsetup_rvalid_i) ign_avsetup <= 1'b1;
      // Dropped OUT packets because no Available OUT Buffer
      if (out_ep_newpkt) drop_avout <= 1'b0;
      else if (out_ep_data_put & !current_setup & !avout_rvalid_i) drop_avout  <= 1'b1;
      // Dropped SETUP/OUT packets because no space in RX FIFO
      if (out_ep_newpkt) drop_rx <= 1'b0;
      else if (out_ep_data_put & !rx_wready) drop_rx <= 1'b1;
    end
  end

  assign event_ign_avsetup_o = ign_avsetup;
  assign event_drop_avout_o  = drop_avout;
  assign event_drop_rx_o     = drop_rx;

  ////////////////
  // Assertions //
  ////////////////
  `ASSERT_INIT(ParamNEndpointsValid, (NEndpoints > 0) && (NEndpoints <= 16))
  `ASSERT_INIT(ParamAVFifoWidthValid, AVFifoWidth > 0)
  `ASSERT_INIT(ParamRXFifoWidthValid, RXFifoWidth > 0)
  `ASSERT_INIT(ParamMaxPktSizeByteValid, MaxPktSizeByte == 64)
  `ASSERT_INIT(ParamNBufValid, NBuf > 1)
  // The SRAM should be large enough for all the buffers of max size (4-byte
  // data width)
  `ASSERT_INIT(ParamSramAwValid, SramAw >= NBufWidth + PktW - 2)

endmodule
