// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB Full-Speed Device Interface core internals
//
//

// This module runs on the 48MHz USB clock
module usbdev_usbif  #(
  parameter int AVFifoWidth = 4,
  parameter int RXFifoWidth = 4,
  parameter int MaxPktSizeByte = 64,
  parameter int NBuf = 4,
  parameter int SramAw = 4,
  parameter int NBufWidth = $clog2(NBuf), // derived parameter
  parameter int PktW = $clog2(MaxPktSizeByte) // derived parameter
) (
  input                            clk_48mhz_i, // 48MHz USB clock
  input                            rst_ni,

  // Pins
  input                            usb_dp_i,
  output logic                     usb_dp_o,
  output logic                     usb_dp_en_o,
  input                            usb_dn_i,
  output logic                     usb_dn_o,
  output logic                     usb_dn_en_o,
  input                            usb_sense_i,
  output logic                     usb_pullup_o,
  output logic                     usb_pullup_en_o,

  // receive (OUT or SETUP) side
  input [11:0]                     rx_setup_i,
  input [11:0]                     rx_out_i,
  input [11:0]                     rx_stall_i,
  input                            av_rvalid_i,
  output logic                     av_rready_o,
  input [AVFifoWidth - 1: 0]       av_rdata_i,
  output logic                     event_av_empty_o,

  output logic                     rx_wvalid_o,
  input                            rx_wready_i,
  output logic [RXFifoWidth - 1:0] rx_wdata_o,
  output logic                     event_rx_full_o,
  output logic                     out_clear_rdy_o,
  output [3:0]                     out_endpoint_o,

  // transmit (IN) side
  input [NBufWidth - 1:0]          in_buf_i,
  input [PktW:0]                   in_size_i,
  input [11:0]                     in_stall_i,
  input [11:0]                     in_rdy_i,
  output logic                     set_sent_o,
  output [3:0]                     in_endpoint_o,

  // memory interface
  output logic                     mem_req_o,
  output logic                     mem_write_o,
  output logic [SramAw-1:0]        mem_addr_o,
  output logic [31:0]              mem_wdata_o,
  input logic [31:0]               mem_rdata_i,

  // control
  input                            enable_i,
  input [6:0]                      devaddr_i,
  output                           clr_devaddr_o,

  // status
  output logic [10:0]              frame_o,
  output logic [1:0]               link_state_o,
  output logic                     link_disconnect_o,
  output logic                     link_reset_o,
  output logic                     link_suspend_o,
  output logic                     link_resume_o,
  output logic                     host_lost_o
);

  logic                              usb_tx_en;

  // Enable -- This is working but should these be swapped so there is no active pull down?
  assign usb_pullup_o = enable_i;
  assign usb_pullup_en_o = 1'b1;

  assign usb_dp_en_o = usb_tx_en;
  assign usb_dn_en_o = usb_tx_en;

  assign clr_devaddr_o = ~enable_i | link_reset_o;

  // OUT or SETUP direction
  logic [PktW:0]                     out_max_used_next, out_max_used;
  logic [PktW-1:0]                   out_ep_put_addr;
  logic [7:0]                        out_ep_data;

  logic [3:0]                        out_ep_current;
  logic                              out_ep_data_put, out_ep_acked, out_ep_rollback;
  logic                              current_setup, all_out_blocked, out_ep_newpkt;
  logic [11:0]                       out_ep_setup, out_ep_full, out_ep_stall;
  logic [11:0]                       setup_blocked, out_blocked;
  logic [31:0]                       wdata;
  logic                              std_write, mem_read;
  logic [SramAw-1:0]                 mem_waddr, mem_raddr;

  assign out_endpoint_o = out_ep_current;

  always_comb begin
    if (out_ep_acked || out_ep_rollback) begin
      out_max_used_next = 0;
    end else if (out_ep_data_put) begin
      // In the normal case <MaxPktSizeByte this is out_max_used <= out_ep_put_addr
      // Following all ones out_max_used will get 1,00..00 and 1,00..01 to cover
      // one and two bytes of the CRC overflowing, then stick at 1,00..01
      out_max_used_next[0] = (out_max_used[PktW] & out_max_used[0]) ? 1'b1 : out_ep_put_addr[0];
      out_max_used_next[PktW - 1: 1] = out_max_used[PktW] ? '0 : out_ep_put_addr[PktW - 1:1];
      out_max_used_next[PktW] = (&out_max_used[PktW - 1:0]) | out_max_used[PktW];
    end else begin
      out_max_used_next = out_max_used;
    end
  end // always_comb

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_max_used <= '0;
      wdata        <= '0;
      std_write    <= 1'b0;
    end else begin
      out_max_used <= out_max_used_next;
      if (out_ep_data_put) begin
        case (out_ep_put_addr[1:0])
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
        // don't write if the address has wrapped (happens for two CRC bytes after max data)
        if (!out_max_used[PktW] && (out_ep_put_addr[1:0] == 2'b11)) begin
          std_write <= 1'b1;
        end else begin
          std_write <= 1'b0;
        end
      end else begin
        std_write <= 1'b0;
      end
    end
  end // always_ff @ (posedge clk_48mhz_i)

  // need extra write at end if packet not multiple of 4 bytes
  assign mem_write_o = std_write |
                       (~out_max_used[PktW] & (out_max_used[1:0] != 2'b11) & out_ep_acked);
  assign mem_waddr = {av_rdata_i, out_max_used[PktW-1:2]};
  assign mem_wdata_o = wdata;
  assign mem_addr_o = mem_write_o ? mem_waddr : mem_raddr;
  assign mem_req_o = mem_read | mem_write_o;
  assign current_setup = out_ep_setup[out_ep_current];  // lint: out_ep_current range was checked

  logic [PktW:0] out_max_minus1;
  // -2 for CRC bytes but +1 for zero-based address to size
  assign out_max_minus1 = out_max_used - 1;

  assign rx_wdata_o = {
      out_ep_current,
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

  assign out_ep_full = {12{all_out_blocked}} | setup_blocked | out_blocked;
  assign out_ep_stall = rx_stall_i;

  // Need to clear IN read if a SETUP is received because it may use the IN channel
  assign out_clear_rdy_o = current_setup & rx_wvalid_o;

  // IN (device to host) transfers
  logic in_ep_acked, in_ep_data_get, in_data_done, in_ep_newpkt, pkt_start_rd;
  logic [11:0] in_ep_data_done;
  logic [PktW-1:0] in_ep_get_addr;
  logic [7:0]      in_ep_data;

  // The protocol engine will automatically generate done for a full-length packet
  // Note: this does the correct thing for sending zero length packets
  assign in_data_done = {1'b0, in_ep_get_addr} == in_size_i;
  always_comb begin
    in_ep_data_done = '0;
    in_ep_data_done[in_endpoint_o] = in_data_done;  // lint: in_endpoint_o range was checked
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

  logic            sof_valid;
  logic [10:0]     frame_index_raw;

  usb_fs_nb_pe #(
    .NumOutEps(12),
    .NumInEps(12),
    .MaxPktSizeByte(MaxPktSizeByte)
  ) u_usb_fs_nb_pe (
    .clk_48mhz_i(clk_48mhz_i),
    .rst_ni(rst_ni),
    .link_reset_i(link_reset_o),

    .usb_p_tx_o(usb_dp_o),
    .usb_n_tx_o(usb_dn_o),
    .usb_p_rx_i(usb_dp_i),
    .usb_n_rx_i(usb_dn_i),
    .usb_tx_en_o(usb_tx_en),

    .dev_addr_i(devaddr_i),

    // out endpoint interfaces
    .out_ep_current_o(out_ep_current),
    .out_ep_newpkt_o(out_ep_newpkt),
    .out_ep_data_put_o(out_ep_data_put),
    .out_ep_put_addr_o(out_ep_put_addr),
    .out_ep_data_o(out_ep_data),
    .out_ep_acked_o(out_ep_acked),
    .out_ep_rollback_o(out_ep_rollback),
    .out_ep_setup_o(out_ep_setup),
    .out_ep_full_i(out_ep_full),
    .out_ep_stall_i(out_ep_stall),

    // in endpoint interfaces
    .in_ep_current_o(in_endpoint_o),
    .in_ep_rollback_o(),
    .in_ep_acked_o(in_ep_acked),
    .in_ep_get_addr_o(in_ep_get_addr),
    .in_ep_data_get_o(in_ep_data_get),
    .in_ep_newpkt_o(in_ep_newpkt),
    .in_ep_stall_i(in_stall_i),
    .in_ep_has_data_i(in_rdy_i),
    .in_ep_data_i(in_ep_data),
    .in_ep_data_done_i(in_ep_data_done),

    // sof interface
    .sof_valid_o(sof_valid),
    .frame_index_o(frame_index_raw)
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
    .usb_rx_dp_i       (usb_dp_i),
    .usb_rx_dn_i       (usb_dn_i),
    .sof_valid_i       (sof_valid),
    .link_disconnect_o (link_disconnect_o),
    .link_reset_o      (link_reset_o),
    .link_suspend_o    (link_suspend_o),
    .link_resume_o     (link_resume_o),
    .link_state_o      (link_state_o),
    .host_lost_o       (host_lost_o)
  );
endmodule
