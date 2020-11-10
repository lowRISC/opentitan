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

`include "prim_assert.sv"

module usb_fs_nb_out_pe #(
  parameter logic [4:0] NumOutEps = 2,
  parameter int unsigned MaxOutPktSizeByte = 32,
  localparam int unsigned OutEpW = $clog2(NumOutEps), // derived parameter
  localparam int unsigned PktW = $clog2(MaxOutPktSizeByte) // derived parameter
) (
  input  logic                   clk_48mhz_i,
  input  logic                   rst_ni,
  input  logic                   link_reset_i,
  input  logic [6:0]             dev_addr_i,

  ////////////////////////
  // endpoint interface //
  ////////////////////////
  output logic [3:0]             out_ep_current_o, // Other signals address to this ep,
                                                   // stable for several cycles
  output logic                   out_ep_data_put_o, // put the data (put addr advances after)
  output logic [PktW - 1:0]      out_ep_put_addr_o, // Offset to put data (0..pktlen)
  output logic [7:0]             out_ep_data_o,
  output logic                   out_ep_newpkt_o, // new packed, current was set
  output logic                   out_ep_acked_o, // good termination, device has acked
  output logic                   out_ep_rollback_o, // bad termination, discard data
  output logic [NumOutEps-1:0]   out_ep_setup_o,
  input  logic [NumOutEps-1:0]   out_ep_full_i, // Cannot accept data
  input  logic [NumOutEps-1:0]   out_ep_stall_i, // Stalled
  input  logic [NumOutEps-1:0]   out_ep_iso_i, // Configure endpoint in isochronous mode

  input logic  [NumOutEps-1:0]   data_toggle_clear_i, // Clear the data toggles for an EP

  /////////////
  // rx path //
  /////////////

  // Strobed on reception of packet.
  input  logic                 rx_pkt_start_i,
  input  logic                 rx_pkt_end_i,
  input  logic                 rx_pkt_valid_i,

  // Most recent packet received.
  input  logic [3:0]           rx_pid_i,
  input  logic [6:0]           rx_addr_i,
  input  logic [3:0]           rx_endp_i,

  // rx_data is pushed into endpoint controller.
  input  logic                 rx_data_put_i,
  input  logic [7:0]           rx_data_i,


  /////////////
  // tx path //
  /////////////

  // Strobe to send new packet.
  output logic                 tx_pkt_start_o,
  input  logic                 tx_pkt_end_i,
  output logic [3:0]           tx_pid_o
);

  // suppress warnings
  logic                      unused_1;
  assign unused_1 = tx_pkt_end_i;

  ////////////////////////////////
  // out transfer state machine //
  ////////////////////////////////
  import usb_consts_pkg::*;

  typedef enum logic [2:0] {
    StIdle,
    StRcvdOut,
    StRcvdDataStart,
    StRcvdDataEnd,
    StRcvdIsoDataEnd
  } state_out_e;

  state_out_e  out_xfr_state;
  state_out_e  out_xfr_state_next;

  logic out_xfr_start;
  logic new_pkt_end;
  logic rollback_data;

  // set when the endpoint buffer is unable to receive the out transfer
  logic nak_out_transfer;

  // data toggle state
  logic [NumOutEps - 1:0] data_toggle_q, data_toggle_d;

  // Decode the rx token
  logic       token_received, out_token_received, setup_token_received;
  logic       invalid_packet_received, data_packet_received, non_data_packet_received;
  logic       bad_data_toggle;
  logic       ep_impl_d, ep_impl_q;
  logic [3:0] out_ep_current_d;

  // 1: If the current transfer is a SETUP, 0: OUT
  logic current_xfer_setup_q;

  // More syntax so can compare with enum
  usb_pid_type_e rx_pid_type;
  usb_pid_e      rx_pid;
  assign rx_pid_type = usb_pid_type_e'(rx_pid_i[1:0]);
  assign rx_pid      = usb_pid_e'(rx_pid_i);

  // Is the specified endpoint actually implemented?
  assign ep_impl_d = {1'b0, rx_endp_i} < NumOutEps;

  assign token_received =
    rx_pkt_end_i &&
    rx_pkt_valid_i &&
    rx_pid_type == UsbPidTypeToken &&
    rx_addr_i == dev_addr_i;

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

  assign out_ep_current_d = ep_impl_d ? rx_endp_i : '0;

  // Make widths work - out_ep_current_d/out_ep_current_o only hold implemented endpoint IDs.
  // These signals can be used to index signals of NumOutEps width.
  // They are only valid if ep_impl_d/q are set, i.e., if the specified endpoint is implemented.
  logic [OutEpW-1:0] out_ep_index;
  logic [OutEpW-1:0] out_ep_index_d;
  assign out_ep_index   = out_ep_current_o[0 +: OutEpW];
  assign out_ep_index_d = out_ep_current_d[0 +: OutEpW];

  assign bad_data_toggle =
    data_packet_received &&
    ep_impl_d &&
    rx_pid_i[3] != data_toggle_q[out_ep_index_d];

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_ep_setup_o <= '0;
    end else begin
      if (setup_token_received && ep_impl_d) begin
        out_ep_setup_o[out_ep_index_d] <= 1'b1;
      end else if (out_token_received && ep_impl_d) begin
        out_ep_setup_o[out_ep_index_d] <= 1'b0;
      end
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_ep_data_o <= 0;
    end else begin
      if (rx_data_put_i) begin
        out_ep_data_o <= rx_data_i;
      end
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

    unique case (out_xfr_state)
      StIdle: begin
        // For unimplemented EPs:
        // - OUT transfers are stalled.
        // - SETUP transfers are ignored.
        if (out_token_received || (setup_token_received && ep_impl_d)) begin
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
        if (ep_impl_q && out_ep_iso_i[out_ep_index] && data_packet_received) begin
          // ISO EP: Don't send a handshake, ignore toggle. Note an unimplemented EP cannot be an
          // ISO EP.
          out_xfr_state_next = StRcvdIsoDataEnd;
        end else if (ep_impl_q && bad_data_toggle && !out_ep_stall_i[out_ep_index]) begin
          // The DATA toggle was wrong (skipped when this EP is stalled)
          // Note: bad_data_toggle is meaningless for unimplemented EPs.
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

        if ((!ep_impl_q || out_ep_stall_i[out_ep_index]) && !current_xfer_setup_q) begin
          // We only send STALL for OUT transfers if the specified EP:
          // - is not implemented,
          // - is not set up.
          // SETUP transfers are not stalled.
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

      StRcvdIsoDataEnd: begin
        out_xfr_state_next = StIdle;

        // An unimplemented EP cannot be in ISO mode, no need to check ep_impl_q here.
        if (out_ep_stall_i[out_ep_index] && !current_xfer_setup_q) begin
          // Send a STALL (something bad happened and the host needs to resolve it)
          tx_pkt_start_o = 1'b1;
          tx_pid_o       = {UsbPidStall}; // STALL
        end else if (nak_out_transfer) begin
          // We got a valid packet, but can't store it (error that the software must resolve)
          rollback_data = 1'b1;
        end else begin
          // We got a valid packet, but we don't send an ACK on the bus
          new_pkt_end    = 1'b1;
          out_ep_acked_o = 1'b1;
        end

      end

      default: out_xfr_state_next = StIdle;
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

  always_comb begin : proc_data_toggle_d
    data_toggle_d = data_toggle_q;

    if (setup_token_received && ep_impl_d) begin
      data_toggle_d[out_ep_index_d] = 1'b0;
    end else if (new_pkt_end) begin
      data_toggle_d[out_ep_index] = ~data_toggle_q[out_ep_index];
    end

    data_toggle_d = data_toggle_d & ~data_toggle_clear_i;
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_toggle_q <= '0; // All endpoints
    end else if (link_reset_i) begin
      data_toggle_q <= '0; // All endpoints
    end else begin
      data_toggle_q <= data_toggle_d;
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_ep_newpkt_o       <= 1'b0;
      out_ep_current_o      <= '0;
      current_xfer_setup_q  <= 1'b0;
      ep_impl_q             <= 1'b0;
    end else begin
      if (out_xfr_start) begin
        out_ep_newpkt_o      <= 1'b1;
        out_ep_current_o     <= out_ep_current_d;
        current_xfer_setup_q <= setup_token_received;
        ep_impl_q            <= ep_impl_d;
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
      end else if (out_ep_data_put_o && out_ep_full_i[out_ep_index]) begin
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
        out_ep_put_addr_o <= out_ep_put_addr_o + 1;
      end
    end
  end

  ////////////////
  // Assertions //
  ////////////////

endmodule
