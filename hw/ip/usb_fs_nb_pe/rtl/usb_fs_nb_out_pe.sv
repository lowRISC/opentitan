// Copyright lowRISC contributors.
// Copyright Luke Valenty (TinyFPGA project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// USB Full Speed Non-Buffered Protocol Engine for OUT/SETUP endpoints
//
// Decode OUT/SETUP requests from host and accept data unless buffers are full
// (SETUP is a special form of OUT and starts a transaction sequence)
//
// Based on usb_fs_out_pe.v from the TinyFPGA-Bootloader project but
// this version contains no packet buffers

module usb_fs_nb_out_pe #(
  parameter NumOutEps = 1,
  parameter MaxOutPktSizeByte = 32,
  parameter PktW = $clog2(MaxOutPktSizeByte),
  parameter OutEpW = $clog2(NumOutEps)
) (
  input                        clk_48mhz_i,
  input                        rst_ni,
  input                        link_reset_i,
  input [6:0]                  dev_addr_i,

  ////////////////////////
  // endpoint interface //
  ////////////////////////
  output logic [3:0]           out_ep_current_o, // Other signals address to this ep
  output logic                 out_ep_data_put_o, // put the data (put addr advances after)
  output logic [PktW - 1:0]    out_ep_put_addr_o, // Offset to put data (0..pktlen)
  output logic [7:0]           out_ep_data_o,
  output logic                 out_ep_newpkt_o, // new packed, current was set
  output logic                 out_ep_acked_o, // good termination, device has acked
  output logic                 out_ep_rollback_o, // bad termination, discard data
  output logic [NumOutEps-1:0] out_ep_setup_o,
  input [NumOutEps-1:0]        out_ep_full_i, // Cannot accept data
  input [NumOutEps-1:0]        out_ep_stall_i, // Stalled

  /////////////
  // rx path //
  /////////////

  // Strobed on reception of packet.
  input                        rx_pkt_start_i,
  input                        rx_pkt_end_i,
  input                        rx_pkt_valid_i,

  // Most recent packet received.
  input [3:0]                  rx_pid_i,
  input [6:0]                  rx_addr_i,
  input [3:0]                  rx_endp_i,

  // rx_data is pushed into endpoint controller.
  input                        rx_data_put_i,
  input [7:0]                  rx_data_i,


  /////////////
  // tx path //
  /////////////

  // Strobe to send new packet.
  output logic                 tx_pkt_start_o,
  input                        tx_pkt_end_i,
  output logic [3:0]           tx_pid_o
);

  // suppress warnings
  logic                      unused_1;
  assign unused_1 = tx_pkt_end_i;

  ////////////////////////////////
  // out transfer state machine //
  ////////////////////////////////
  import usb_consts_pkg::*;

  typedef enum logic [1:0] {
    StIdle          = 2'h0,
    StRcvdOut       = 2'h1,
    StRcvdDataStart = 2'h2,
    StRcvdDataEnd   = 2'h3
  } state_out_e;

  state_out_e  out_xfr_state;
  state_out_e  out_xfr_state_next;

  logic out_xfr_start;
  logic new_pkt_end;
  logic rollback_data;

  // set when the endpoint buffer is unable to receive the out transfer
  logic nak_out_transfer;

  // data toggle state
  logic [NumOutEps - 1:0] data_toggle;

  // Make widths work
  logic [OutEpW - 1 : 0]    out_ep_index;
  assign out_ep_index = out_ep_current_o[0 +: OutEpW];

  // Decode the rx token
  logic token_received, out_token_received, setup_token_received;
  logic invalid_packet_received, data_packet_received, non_data_packet_received;
  logic bad_data_toggle;

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
    rx_endp_i < NumOutEps;

  assign out_token_received =
    token_received &&
    rx_pid == UsbPidOut;

  assign setup_token_received =
    token_received &&
    rx_pid == UsbPidSetup;

  assign invalid_packet_received =
    rx_pkt_end_i &&
    !rx_pkt_valid_i;

  assign data_packet_received =
    rx_pkt_end_i &&
    rx_pkt_valid_i &&
    ((rx_pid == UsbPidData0) || (rx_pid == UsbPidData1));


  assign non_data_packet_received =
    rx_pkt_end_i &&
    rx_pkt_valid_i &&
    !((rx_pid == UsbPidData0) || (rx_pid == UsbPidData1));

  assign bad_data_toggle =
    data_packet_received &&
    rx_pid_i[3] != data_toggle[rx_endp_i[0 +: OutEpW]]; // lint: rx_endp_i range was checked


  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_ep_setup_o <= 0;
    end else begin
      if (setup_token_received) begin
        out_ep_setup_o[rx_endp_i[0 +: OutEpW]] <= 1; // lint: rx_endp_i range was checked
      end else if (out_token_received) begin
        out_ep_setup_o[rx_endp_i[0 +: OutEpW]] <= 0; // lint: rx_endp_i range was checked
      end
    end
  end

  always_ff @(posedge clk_48mhz_i) begin
    if (rx_data_put_i) begin
      out_ep_data_o <= rx_data_i;
    end
  end

  ////////////////////////////////
  // out transfer state machine //
  ////////////////////////////////

  always_comb begin
    out_ep_acked_o = 1'b0;
    out_xfr_start = 1'b0;
    out_xfr_state_next = out_xfr_state;
    tx_pkt_start_o = 1'b0;
    tx_pid_o = 4'b0000;
    new_pkt_end = 1'b0;
    rollback_data = 1'b0;

    case (out_xfr_state)
      StIdle: begin
        if (out_token_received || setup_token_received) begin
          out_xfr_state_next = StRcvdOut;
          out_xfr_start = 1'b1;
        end else begin
          out_xfr_state_next = StIdle;
        end
      end

      StRcvdOut: begin
        if (rx_pkt_start_i) begin
          out_xfr_state_next = StRcvdDataStart;
        end else begin
          out_xfr_state_next = StRcvdOut;
        end
      end

      StRcvdDataStart: begin
        if (bad_data_toggle) begin
          out_xfr_state_next = StIdle;
          rollback_data = 1'b1;
          tx_pkt_start_o = 1'b1;
          tx_pid_o = {UsbPidAck}; // ACK by spec because this is most likely previous ACK was lost
        end else if (invalid_packet_received || non_data_packet_received) begin
          // in these cases eg bad CRC, send no response (not a NAK)
          out_xfr_state_next = StIdle;
          rollback_data = 1'b1;
        end else if (data_packet_received) begin
          out_xfr_state_next = StRcvdDataEnd;
        end else begin
          out_xfr_state_next = StRcvdDataStart;
        end
      end

      StRcvdDataEnd: begin
        out_xfr_state_next = StIdle;
        tx_pkt_start_o = 1'b1;

        if (out_ep_stall_i[out_ep_index]) begin // lint: out_ep_index range was checked
          tx_pid_o = {UsbPidStall}; // STALL
        end else if (nak_out_transfer) begin
          tx_pid_o = {UsbPidNak}; // NAK -- the endpoint could not accept the data at the moment
          rollback_data = 1'b1;
        end else begin
          tx_pid_o = {UsbPidAck}; // ACK
          new_pkt_end = 1'b1;
          out_ep_acked_o = 1'b1;
        end
      end

      // Add default if state space no longer exactly fits in bitwidth
      // default begin
      //  out_xfr_state_next = StIdle;
      // end
    endcase
  end

  // could flop this if needed
  assign out_ep_rollback_o = rollback_data;

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_xfr_state <= StIdle;
    end else begin
      out_xfr_state <= link_reset_i ? StIdle : out_xfr_state_next;
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_toggle <= '0; // All endpoints
    end else if (link_reset_i) begin
      data_toggle <= '0; // All endpoints
    end else begin
      if (setup_token_received) begin
        data_toggle[rx_endp_i[0 +: OutEpW]] <= 1'b0; // lint: rx_endp_i range was checked
      end else if (new_pkt_end) begin
        data_toggle[out_ep_index] <= !data_toggle[out_ep_index]; // lint: range was checked
      end
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_ep_newpkt_o <= 1'b0;
      out_ep_current_o <= '0;
    end else begin
      if (out_xfr_start) begin
        out_ep_newpkt_o <= 1'b1;
        out_ep_current_o <= rx_endp_i;
      end else begin
        out_ep_newpkt_o <= 1'b0;
      end
    end
  end

  // put data strobe follows the rx strobe (which will latch the data)
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_ep_data_put_o <= 1'b0;
    end else begin
      out_ep_data_put_o <= ((out_xfr_state == StRcvdDataStart) && rx_data_put_i);
    end
  end

  // nack an OUT if any data comes in with the endpoint full
  // Note that if there is a full size packet buffer this will only be all or nothing
  // but in the case there was a FIFO with less than a max packet size free you
  // could get lucky and the packet received be small and fit with no need to NAK
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      nak_out_transfer <= 1'b0;
    end else begin
      if ((out_xfr_state == StIdle) || (out_xfr_state == StRcvdOut)) begin
        nak_out_transfer <= 1'b0;
      end else if (out_ep_data_put_o && out_ep_full_i[out_ep_index]) begin // lint: range checked
        nak_out_transfer <= 1'b1;
      end
    end
  end

  // address increment whenever there is a data put unless
  // -- already going to NAK transaction and replay things
  // -- the address is at max packet size
  // NOTE if more than max packet size received then data is lost
  logic increment_addr;
  assign increment_addr = !nak_out_transfer && (~&out_ep_put_addr_o) && out_ep_data_put_o;

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_ep_put_addr_o <= '0;
    end else begin
      if (out_xfr_state == StRcvdOut) begin
        out_ep_put_addr_o <= '0;
      end else if ((out_xfr_state == StRcvdDataStart) && increment_addr) begin
        out_ep_put_addr_o <= out_ep_put_addr_o + 1'b1;
      end
    end
  end

endmodule
