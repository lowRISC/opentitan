// Copyright lowRISC contributors.
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
  input  logic                     usb_se0_i,

  output logic                     usb_d_o,
  output logic                     usb_se0_o,
  output logic                     usb_oe_o,

  output logic                     usb_pullup_en_o,
  input  logic                     usb_sense_i,

  // receive (OUT or SETUP) side
  input  logic [NEndpoints-1:0]    rx_setup_i,
  input  logic [NEndpoints-1:0]    rx_out_i,
  input  logic [NEndpoints-1:0]    rx_stall_i,
  input  logic                     av_rvalid_i,
  output logic                     av_rready_o,
  input  logic [AVFifoWidth - 1: 0]av_rdata_i,
  output logic                     event_av_empty_o,

  output logic                     rx_wvalid_o,
  input  logic                     rx_wready_i,
  output logic [RXFifoWidth - 1:0] rx_wdata_o,
  output logic                     event_rx_full_o,
  output logic                     setup_received_o,
  output [3:0]                     out_endpoint_o,

  // transmit (IN) side
  input  logic [NBufWidth - 1:0]   in_buf_i,
  input  logic [PktW:0]            in_size_i,
  input  logic [NEndpoints-1:0]    in_stall_i,
  input  logic [NEndpoints-1:0]    in_rdy_i,
  output logic                     set_sent_o,
  output [3:0]                     in_endpoint_o,

  // memory interface
  output logic                     mem_req_o,
  output logic                     mem_write_o,
  output logic [SramAw-1:0]        mem_addr_o,
  output logic [31:0]              mem_wdata_o,
  input  logic [31:0]              mem_rdata_i,

  // control
  input  logic                     enable_i,
  input  logic [6:0]               devaddr_i,
  output logic                     clr_devaddr_o,
  input  logic [NEndpoints-1:0]    ep_iso_i,
  input  logic                     cfg_eop_single_bit_i, // 1: detect a single SE0 bit as EOP
  input  logic                     tx_osc_test_mode_i, // Oscillator test mode: constant JK output
  input  logic [NEndpoints-1:0]    data_toggle_clear_i, // Clear the data toggles for an EP

  // status
  output logic                     frame_start_o,
  output logic [10:0]              frame_o,
  output logic [2:0]               link_state_o,
  output logic                     link_disconnect_o,
  output logic                     link_connect_o,
  output logic                     link_reset_o,
  output logic                     link_suspend_o,
  output logic                     link_resume_o,
  output logic                     link_in_err_o,
  output logic                     host_lost_o,
  output logic                     rx_crc_err_o,
  output logic                     rx_pid_err_o,
  output logic                     rx_bitstuff_err_o
);

  assign usb_pullup_en_o = enable_i;

  // OUT or SETUP direction
  logic [PktW:0]                     out_max_used_d, out_max_used_q;
  logic [PktW-1:0]                   out_ep_put_addr;
  logic [7:0]                        out_ep_data;

  logic [3:0]                        out_ep_current;
  logic                              out_ep_data_put, out_ep_acked, out_ep_rollback;
  logic                              current_setup, all_out_blocked, out_ep_newpkt;
  logic [NEndpoints-1:0]             out_ep_setup, out_ep_full, out_ep_stall;
  logic [NEndpoints-1:0]             setup_blocked, out_blocked;
  logic [31:0]                       wdata;
  logic                              mem_read;
  logic [SramAw-1:0]                 mem_waddr, mem_raddr;
  logic                              link_reset;
  logic                              sof_valid;

  // Make sure out_endpoint_o can safely be used to index signals of NEndpoints width.
  assign out_endpoint_o = (out_ep_current < NEndpoints) ? out_ep_current : '0;
  assign link_reset_o   = link_reset;
  assign clr_devaddr_o  = ~enable_i | link_reset;
  assign frame_start_o  = sof_valid;

  always_comb begin
    if (out_ep_acked || out_ep_rollback) begin
      out_max_used_d = 0;

    end else if (out_ep_data_put) begin
      // In the normal case <MaxPktSizeByte this is out_max_used_q <= out_ep_put_addr
      // Following all ones out_max_used_q will get 1,00..00 and 1,00..01 to cover
      // one and two bytes of the CRC overflowing, then stick at 1,00..01
      if (out_max_used_q < MaxPktSizeByte - 1) begin
        out_max_used_d = out_ep_put_addr;
      end else if (out_max_used_q < MaxPktSizeByte + 1) begin
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
  assign std_write_d = out_ep_data_put & ((out_max_used_q < MaxPktSizeByte - 1) &
      (out_ep_put_addr[1:0] == 2'b11));

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_max_used_q <= '0;
      wdata          <= '0;
      std_write_q    <= 1'b0;
    end else begin
      out_max_used_q <= out_max_used_d;
      std_write_q    <= std_write_d;
      if (out_ep_data_put) begin
        unique case (out_ep_put_addr[1:0])
          0: begin
            wdata[7:0] <= out_ep_data;
          end
          1: begin
            wdata[15:8] <= out_ep_data;
          end
          2: begin
            wdata[23:16] <= out_ep_data;
          end
          3: begin
            wdata[31:24] <= out_ep_data;
          end
        endcase
      end
    end
  end // always_ff @ (posedge clk_48mhz_i)

  // need extra write at end if packet not multiple of 4 bytes
  assign mem_write_o = std_write_q |
                       (~out_max_used_q[PktW] & (out_max_used_q[1:0] != 2'b11) & out_ep_acked);
  assign mem_waddr = {av_rdata_i, out_max_used_q[PktW-1:2]};
  assign mem_wdata_o = wdata;
  assign mem_addr_o = mem_write_o ? mem_waddr : mem_raddr;
  assign mem_req_o = mem_read | mem_write_o;
  assign current_setup = out_ep_setup[out_endpoint_o];

  logic [PktW:0] out_max_minus1;
  // -2 for CRC bytes but +1 for zero-based address to size
  assign out_max_minus1 = out_max_used_q - 1;

  assign rx_wdata_o = {
      out_endpoint_o,
      current_setup,
      out_max_minus1,
      av_rdata_i
  };
  assign rx_wvalid_o = out_ep_acked & ~all_out_blocked;
  // Pop the available fifo after the write that used the previous value
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      av_rready_o <= 1'b0;
    end else begin
      av_rready_o <= rx_wvalid_o;
    end
  end

  // full here covers the software blocking by clearing the enable
  assign setup_blocked = out_ep_setup & ~rx_setup_i;
  assign out_blocked = ~out_ep_setup & ~rx_out_i;
  // full also covers being blocked because the hardware can't take any transaction
  assign all_out_blocked = (~rx_wready_i) | (~av_rvalid_i);
  // These are used to raise appropriate interrupt
  assign event_av_empty_o = out_ep_newpkt & (~av_rvalid_i);
  assign event_rx_full_o = out_ep_newpkt & (~rx_wready_i);

  assign out_ep_full = {NEndpoints{all_out_blocked}} | setup_blocked | out_blocked;
  assign out_ep_stall = rx_stall_i;

  // Need to clear IN read if a SETUP is received because it may use the IN channel
  // This will not trigger, if the AV Buffer is empty, in that case we have replied
  // with a NAK, which is illegal anyway
  assign setup_received_o = current_setup & rx_wvalid_o;

  // IN (device to host) transfers
  logic                  in_ep_acked, in_ep_data_get, in_data_done, in_ep_newpkt, pkt_start_rd;
  logic [NEndpoints-1:0] in_ep_data_done;
  logic [PktW-1:0]       in_ep_get_addr;
  logic [7:0]            in_ep_data;
  logic [3:0]            in_ep_current;

  // Make sure in_endpoint_o can safely be used to index signals of NEndpoints width.
  assign in_endpoint_o = (in_ep_current < NEndpoints) ? in_ep_current : '0;

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
  assign set_sent_o = in_ep_acked;

  logic [10:0]     frame_index_raw;

  usb_fs_nb_pe #(
    .NumOutEps      (NEndpoints),
    .NumInEps       (NEndpoints),
    .MaxPktSizeByte (MaxPktSizeByte)
  ) u_usb_fs_nb_pe (
    .clk_48mhz_i           (clk_48mhz_i),
    .rst_ni                (rst_ni),
    .link_reset_i          (link_reset),

    .cfg_eop_single_bit_i  (cfg_eop_single_bit_i),
    .tx_osc_test_mode_i    (tx_osc_test_mode_i),
    .data_toggle_clear_i   (data_toggle_clear_i),

    .usb_d_i               (usb_d_i),
    .usb_se0_i             (usb_se0_i),
    .usb_d_o               (usb_d_o),
    .usb_se0_o             (usb_se0_o),
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
    .out_ep_full_i         (out_ep_full),
    .out_ep_stall_i        (out_ep_stall),
    .out_ep_iso_i          (ep_iso_i),

    // in endpoint interfaces
    .in_ep_current_o       (in_ep_current),
    .in_ep_rollback_o      (link_in_err_o),
    .in_ep_acked_o         (in_ep_acked),
    .in_ep_get_addr_o      (in_ep_get_addr),
    .in_ep_data_get_o      (in_ep_data_get),
    .in_ep_newpkt_o        (in_ep_newpkt),
    .in_ep_stall_i         (in_stall_i),
    .in_ep_has_data_i      (in_rdy_i),
    .in_ep_data_i          (in_ep_data),
    .in_ep_data_done_i     (in_ep_data_done),
    .in_ep_iso_i           (ep_iso_i),

    // error signals
    .rx_crc_err_o          (rx_crc_err_o),
    .rx_pid_err_o          (rx_pid_err_o),
    .rx_bitstuff_err_o     (rx_bitstuff_err_o),

    // sof interface
    .sof_valid_o           (sof_valid),
    .frame_index_o         (frame_index_raw)
  );

  // us_tick ticks for one cycle every us
  logic [5:0]   ns_cnt;
  logic         us_tick;

  assign us_tick = (ns_cnt == 6'd48);
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ns_cnt <= '0;
    end else begin
      if (us_tick) begin
        ns_cnt <= '0;
      end else begin
        ns_cnt <= ns_cnt + 1'b1;
      end
    end
  end

  // Capture frame number (host sends evert 1ms)
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      frame_o <= '0;
    end else begin
      if (sof_valid) begin
        frame_o <= frame_index_raw;
      end
    end
  end

  usbdev_linkstate u_usbdev_linkstate (
    .clk_48mhz_i       (clk_48mhz_i),
    .rst_ni            (rst_ni),
    .us_tick_i         (us_tick),
    .usb_sense_i       (usb_sense_i),
    .usb_rx_d_i        (usb_d_i),
    .usb_rx_se0_i      (usb_se0_i),
    .sof_valid_i       (sof_valid),
    .link_disconnect_o (link_disconnect_o),
    .link_connect_o    (link_connect_o),
    .link_reset_o      (link_reset),
    .link_suspend_o    (link_suspend_o),
    .link_resume_o     (link_resume_o),
    .link_state_o      (link_state_o),
    .host_lost_o       (host_lost_o)
  );

  ////////////////
  // Assertions //
  ////////////////

  // Specified endpoint is not implemented.
  `ASSERT(UsbIfOutEndPImpl, out_ep_newpkt |-> (out_endpoint_o == out_ep_current), clk_48mhz_i)
  `ASSERT(UsbIfInEndPImpl, in_ep_newpkt |-> (in_endpoint_o == in_ep_current), clk_48mhz_i)

endmodule
