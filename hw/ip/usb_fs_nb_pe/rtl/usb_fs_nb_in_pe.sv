// Copyright lowRISC contributors.
// Copyright Luke Valenty (TinyFPGA project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// USB Full Speed Non-Buffered Protocol Engine for IN endpoints
//
// Decode IN requests from host and respond with data if there is any
//
// Based on usb_fs_in_pe.v from the TinyFPGA-Bootloader project but
// this version contains no packet buffers

module usb_fs_nb_in_pe #(
  parameter logic [4:0] NumInEps = 11,
  parameter MaxInPktSizeByte = 32,
  parameter PktW = $clog2(MaxInPktSizeByte),
  parameter InEpW = $clog2(NumInEps)
) (
  input                     clk_48mhz_i,
  input                     rst_ni,
  input                     link_reset_i,
  input [6:0]               dev_addr_i,


  ////////////////////
  // endpoint interface
  ////////////////////
  output logic [3:0]        in_ep_current_o, // Other signals addressed to this ep
  output logic              in_ep_rollback_o, // Bad termination, rollback transaction
  output logic              in_ep_acked_o, // good termination, transaction complete
  output logic [PktW - 1:0] in_ep_get_addr_o, // Offset requested (0..pktlen)
  output logic              in_ep_data_get_o, // Accept data (get_addr advances too)
  output logic              in_ep_newpkt_o, // New IN packet starting (with in_ep_current_o update)
  input [NumInEps-1:0]      in_ep_stall_i, // Endpoint in a stall state
  input [NumInEps-1:0]      in_ep_has_data_i, // Endpoint has data to supply
  input [7:0]               in_ep_data_i, // Data for current get_addr
  input [NumInEps-1:0]      in_ep_data_done_i, // Set when out of data

  ////////////////////
  // rx path
  ////////////////////

  // Strobed on reception of packet.
  input                     rx_pkt_start_i,
  input                     rx_pkt_end_i,
  input                     rx_pkt_valid_i,

  // Most recent packet received.
  input [3:0]               rx_pid_i,
  input [6:0]               rx_addr_i,
  input [3:0]               rx_endp_i,

  ////////////////////
  // tx path
  ////////////////////

  // Strobe to send new packet.
  output logic              tx_pkt_start_o,
  input                     tx_pkt_end_i,
  // Packet type to send
  output logic [3:0]        tx_pid_o,

  // Data payload to send if any
  output                    tx_data_avail_o,
  input                     tx_data_get_i,
  output logic [7:0]        tx_data_o
);
  // suppress warnings
  logic                      unused_1, unused_2;
  assign unused_1 = tx_pkt_end_i;
  assign unused_2 = rx_pkt_start_i;

  ////////////////////////////////////////////////////////////////////////////////
  // in transfer state machine
  ////////////////////////////////////////////////////////////////////////////////

  import usb_consts_pkg::*;

  typedef enum logic [1:0] {
    StIdle     = 2'h0,
    StRcvdIn   = 2'h1,
    StSendData = 2'h2,
    StWaitAck  = 2'h3
  } state_in_e;

  state_in_e  in_xfr_state;
  state_in_e  in_xfr_state_next;

  logic in_xfr_end;

  assign in_ep_acked_o = in_xfr_end;

  // data toggle state
  logic [NumInEps - 1:0] data_toggle;

  // endpoint data buffer
  logic                    token_received, setup_token_received, in_token_received, ack_received;
  logic                    more_data_to_send;

  // Make widths work
  logic [InEpW - 1 : 0]    in_ep_index;
  assign in_ep_index = in_ep_current_o[0 +: InEpW];

  // More syntax so can compare with enum
  usb_pid_type_e rx_pid_type;
  usb_pid_e      rx_pid;
  assign rx_pid_type = usb_pid_type_e'(rx_pid_i[1:0]);
  assign rx_pid      = usb_pid_e'(rx_pid_i);

  assign token_received =
    rx_pkt_end_i &&
    rx_pkt_valid_i &&
    rx_pid_type == UsbPidTypeToken &&
    rx_addr_i == dev_addr_i &&
    {1'b0, rx_endp_i} < NumInEps;

  assign setup_token_received =
    token_received &&
    rx_pid == UsbPidSetup;

  assign in_token_received =
    token_received &&
    rx_pid == UsbPidIn;

  assign ack_received =
    rx_pkt_end_i &&
    rx_pkt_valid_i &&
    rx_pid == UsbPidAck;

  assign more_data_to_send = ~in_ep_data_done_i[in_ep_index];  // lint: in_ep_index range was checked

  assign tx_data_avail_o = (in_xfr_state == StSendData) && more_data_to_send;

  ////////////////////////////////////////////////////////////////////////////////
  // in transfer state machine
  ////////////////////////////////////////////////////////////////////////////////

  logic rollback_in_xfr;

  always_comb begin
    in_xfr_state_next = in_xfr_state;
    in_xfr_end = 1'b0;
    tx_pkt_start_o = 1'b0;
    tx_pid_o = 4'b0000;
    rollback_in_xfr = 1'b0;
    case (in_xfr_state)
      StIdle: begin
        if (in_token_received) begin
          in_xfr_state_next = StRcvdIn;
        end else begin
          in_xfr_state_next = StIdle;
        end
      end

      StRcvdIn: begin
        tx_pkt_start_o = 1'b1; // Need to transmit NACK/STALL or DATA

        if (in_ep_stall_i[in_ep_index]) begin  // lint: in_ep_index range was checked
          in_xfr_state_next = StIdle;
          tx_pid_o = {UsbPidStall}; // STALL
        end else if (in_ep_has_data_i[in_ep_index]) begin  // lint: in_ep_index range was checked
          in_xfr_state_next = StSendData;
          tx_pid_o = {data_toggle[in_ep_index], 1'b0, {UsbPidTypeData}}; // DATA0/1 lint: checked
        end else begin
          in_xfr_state_next = StIdle;
          tx_pid_o = {UsbPidNak}; // NAK
        end
      end

      StSendData: begin
        // Use &in_ep_get_addr so width can vary, looking for all ones
        if ((!more_data_to_send) || ((&in_ep_get_addr_o) && tx_data_get_i)) begin
          in_xfr_state_next = StWaitAck;
        end else begin
          in_xfr_state_next = StSendData;
        end
      end

      StWaitAck: begin
        // FIXME: need to handle smash/timeout
        if (ack_received) begin
          in_xfr_state_next = StIdle;
          in_xfr_end = 1'b1;
        end else if (in_token_received) begin
          in_xfr_state_next = StRcvdIn;
          rollback_in_xfr = 1'b1;
        end else if (rx_pkt_end_i) begin
          in_xfr_state_next = StIdle;
          rollback_in_xfr = 1'b1;
        end else begin
          in_xfr_state_next = StWaitAck;
        end
      end
    endcase
  end

  always_ff @(posedge clk_48mhz_i) begin
    tx_data_o <= in_ep_data_i;
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      in_xfr_state <= StIdle;
      in_ep_rollback_o <= 1'b0;
    end else if (link_reset_i) begin
      in_xfr_state <= StIdle;
      in_ep_rollback_o <= 1'b0;
    end else begin
      in_xfr_state <= in_xfr_state_next;
      in_ep_rollback_o <= rollback_in_xfr;
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      in_ep_get_addr_o <= '0;
    end else begin
      if (in_xfr_state == StIdle) begin
        in_ep_get_addr_o <= '0;
      end else if ((in_xfr_state == StSendData) && tx_data_get_i) begin
        in_ep_get_addr_o <= in_ep_get_addr_o + 1'b1;
      end
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      in_ep_newpkt_o <= 1'b0;
      in_ep_current_o <= '0;
    end else begin
      if (in_token_received) begin
        in_ep_current_o <= rx_endp_i;
        in_ep_newpkt_o <= 1'b1;
      end else begin
        in_ep_newpkt_o <= 1'b0;
      end
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_toggle <= '0; // Clear for all endpoints
    end else if (link_reset_i) begin
      data_toggle <= '0; // Clear for all endpoints
    end else begin
      if (setup_token_received) begin
        // Ok because token_recieved only triggers if rx_endp_i is in range
        data_toggle[rx_endp_i[0 +: InEpW]] <= 1'b1;
      end else if ((in_xfr_state == StWaitAck) && ack_received) begin
        data_toggle[in_ep_index] <= ~data_toggle[in_ep_index]; // lint: range was checked
      end
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      in_ep_data_get_o <= 1'b0;
    end else begin
      if ((in_xfr_state == StSendData) && tx_data_get_i) begin
        in_ep_data_get_o <= 1'b1;
      end else begin
        in_ep_data_get_o <= 1'b0;
      end
    end
  end


endmodule
