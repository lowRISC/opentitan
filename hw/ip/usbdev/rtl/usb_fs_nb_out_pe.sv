// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Copyright Luke Valenty (TinyFPGA project, https://github.com/tinyfpga/TinyFPGA-Bootloader).

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
  // Targeting 17 bit times for the timeout. The counter runs on the 48 MHz
  // clock. The SOP delay to rx_pkt_start_i is 3 bit times, but the two
  // packets go in the same direction, so this is negated. This timeout
  // originates from Section 7.1.19.1 of the USB 2.0 specification.
  parameter int unsigned AckTimeoutCnt = 17 * 4,
  localparam int unsigned OutEpW = $clog2(NumOutEps), // derived parameter
  localparam int unsigned PktW = $clog2(MaxOutPktSizeByte), // derived parameter
  localparam int unsigned AckTimeoutCntW = $clog2(AckTimeoutCnt) // derived parameter
) (
  input  logic                   clk_48mhz_i,
  input  logic                   rst_ni,
  input  logic                   link_reset_i,
  input  logic                   link_active_i,
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
  input  logic [NumOutEps-1:0]   out_ep_enabled_i, // Endpoint is enabled and produces handshakes
  input  logic [NumOutEps-1:0]   out_ep_control_i, // Is a control endpoint: Accepts SETUP packets
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
  logic                        unused_1;
  assign unused_1 = tx_pkt_end_i;

  ///////////////////////////////////
  // out transaction state machine //
  ///////////////////////////////////
  import usb_consts_pkg::*;

  typedef enum logic [2:0] {
    StIdle,
    StRcvdOut,
    StRcvdDataStart,
    StRcvdDataEnd,
    StRcvdIsoDataEnd
  } state_out_e;

  state_out_e  out_xact_state;
  state_out_e  out_xact_state_next;

  logic out_xact_start;
  logic new_pkt_end;
  logic rollback_data;

  // set when the endpoint buffer is unable to receive the out transaction
  logic nak_out_transaction;

  // data toggle state
  logic [NumOutEps - 1:0] data_toggle_q, data_toggle_d;

  // Decode the rx token
  logic       token_received, out_token_received, setup_token_received;
  logic       invalid_packet_received, data_packet_received, non_data_packet_received;
  logic       bad_data_toggle;
  logic       ep_in_hw, ep_active, ep_is_control;
  logic [3:0] out_ep_current_d;

  // 1: If the current transaction is a SETUP, 0: OUT
  logic current_xact_setup_q;

  // More syntax so can compare with enum
  usb_pid_type_e rx_pid_type;
  usb_pid_e      rx_pid;
  assign rx_pid_type = usb_pid_type_e'(rx_pid_i[1:0]);
  assign rx_pid      = usb_pid_e'(rx_pid_i);

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

  // Is the specified endpoint actually implemented in hardware?
  assign ep_in_hw = {1'b0, rx_endp_i} < NumOutEps;
  assign out_ep_current_d = ep_in_hw ? rx_endp_i : '0;

  // Make widths work - out_ep_current_d/out_ep_current_o only hold implemented endpoint IDs.
  // These signals can be used to index signals of NumOutEps width.
  // They are only valid if ep_in_hw is set, i.e., if the specified endpoint is implemented.
  logic [OutEpW-1:0] out_ep_index;
  logic [OutEpW-1:0] out_ep_index_d;
  assign out_ep_index   = out_ep_current_o[0 +: OutEpW];
  assign out_ep_index_d = out_ep_current_d[0 +: OutEpW];

  // Is the endpoint active?
  assign ep_active = out_ep_enabled_i[out_ep_index_d] & ep_in_hw;
  assign ep_is_control = out_ep_control_i[out_ep_index_d];

  assign bad_data_toggle =
    data_packet_received &&
    ep_active &&
    rx_pid_i[3] != data_toggle_q[out_ep_index_d];

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_ep_setup_o <= '0;
    end else begin
      if (setup_token_received && ep_active) begin
        out_ep_setup_o[out_ep_index_d] <= 1'b1;
      end else if (out_token_received && ep_active) begin
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

  ///////////////////////////////////
  // out transaction state machine //
  ///////////////////////////////////

  logic [AckTimeoutCntW-1:0] timeout_cntdown_d, timeout_cntdown_q;

  always_comb begin
    out_ep_acked_o = 1'b0;
    out_xact_start = 1'b0;
    out_xact_state_next = out_xact_state;
    tx_pkt_start_o = 1'b0;
    tx_pid_o = 4'b0000;
    new_pkt_end = 1'b0;
    rollback_data = 1'b0;
    timeout_cntdown_d = AckTimeoutCnt[AckTimeoutCntW-1:0];

    unique case (out_xact_state)
      StIdle: begin
        // For unimplemented EPs, transactions are ignored.
        // SETUP transactions are also ignored for non-control EPs.
        if (ep_active && (out_token_received || (setup_token_received && ep_is_control))) begin
          out_xact_state_next = StRcvdOut;
          out_xact_start = 1'b1;
        end else begin
          out_xact_state_next = StIdle;
        end
      end

      StRcvdOut: begin
        // The spec says we have up to 18 bit times to wait for the host's
        // data packet. If it doesn't arrive in time, we must invalidate the
        // transaction.
        timeout_cntdown_d = timeout_cntdown_q - 1'b1;

        if (rx_pkt_start_i) begin
          out_xact_state_next = StRcvdDataStart;
        end else if (timeout_cntdown_q == '0) begin
          out_xact_state_next = StIdle;
        end else begin
          out_xact_state_next = StRcvdOut;
        end
      end

      StRcvdDataStart: begin
        if (!ep_is_control && out_ep_iso_i[out_ep_index] && data_packet_received) begin
          // ISO EP: Don't send a handshake, ignore toggle.
          // But ignore iso bit for endpoints marked control. This is
          // a configuration error.
          out_xact_state_next = StRcvdIsoDataEnd;
        end else if (bad_data_toggle && !out_ep_stall_i[out_ep_index]) begin
          // The DATA toggle was wrong (skipped when this EP is stalled)
          // Note: bad_data_toggle is meaningless for unimplemented EPs.
          out_xact_state_next = StIdle;
          rollback_data = 1'b1;
          tx_pkt_start_o = 1'b1;
          tx_pid_o = {UsbPidAck}; // ACK by spec because this is most likely previous ACK was lost
        end else if (invalid_packet_received || non_data_packet_received) begin
          // in these cases eg bad CRC, send no response (not a NAK)
          out_xact_state_next = StIdle;
          rollback_data = 1'b1;
        end else if (data_packet_received) begin
          out_xact_state_next = StRcvdDataEnd;
        end else begin
          out_xact_state_next = StRcvdDataStart;
        end
      end

      StRcvdDataEnd: begin
        out_xact_state_next = StIdle;
        tx_pkt_start_o = 1'b1;

        if (current_xact_setup_q) begin
          // SETUP transactions end here
          if (nak_out_transaction | out_ep_full_i[out_ep_index]) begin
            // SETUP transactions that fail to be received are dropped without a response.
            tx_pkt_start_o = 1'b0;
            rollback_data = 1'b1;
          end else begin
            tx_pid_o = {UsbPidAck};
            new_pkt_end = 1'b1;
            out_ep_acked_o = 1'b1;
          end
        end else begin
          // Non-isochronous OUT transactions end here
          if (out_ep_stall_i[out_ep_index]) begin
            tx_pid_o = {UsbPidStall}; // STALL
          end else if (nak_out_transaction | out_ep_full_i[out_ep_index]) begin
            tx_pid_o = {UsbPidNak}; // NAK -- the endpoint could not accept the data at the moment
            rollback_data = 1'b1;
          end else begin
            tx_pid_o = {UsbPidAck}; // ACK
            new_pkt_end = 1'b1;
            out_ep_acked_o = 1'b1;
          end
        end
      end

      StRcvdIsoDataEnd: begin
        // Isochronous OUT transactions end here
        out_xact_state_next = StIdle;

        if (nak_out_transaction | out_ep_full_i[out_ep_index]) begin
          // We got a valid packet, but can't store it (error that the software must resolve)
          rollback_data = 1'b1;
        end else begin
          // We got a valid packet, but we don't send an ACK on the bus
          new_pkt_end    = 1'b1;
          out_ep_acked_o = 1'b1;
        end

      end

      default: out_xact_state_next = StIdle;
    endcase
  end

  `ASSERT(OutXactStateValid_A,
    out_xact_state inside {StIdle, StRcvdOut, StRcvdDataStart, StRcvdDataEnd, StRcvdIsoDataEnd},
    clk_48mhz_i)

  // could flop this if needed
  assign out_ep_rollback_o = rollback_data;

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      timeout_cntdown_q <= AckTimeoutCnt[AckTimeoutCntW-1:0];
    end else begin
      timeout_cntdown_q <= timeout_cntdown_d;
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_xact_state <= StIdle;
    end else begin
      out_xact_state <= link_reset_i ? StIdle : out_xact_state_next;
    end
  end

  always_comb begin : proc_data_toggle_d
    data_toggle_d = data_toggle_q;

    if (setup_token_received && ep_active) begin
      data_toggle_d[out_ep_index_d] = 1'b0;
    end else if (new_pkt_end) begin
      data_toggle_d[out_ep_index] = ~data_toggle_q[out_ep_index];
    end

    data_toggle_d = data_toggle_d & ~data_toggle_clear_i;
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_toggle_q <= '0; // All endpoints
    end else if (link_reset_i || !link_active_i) begin
      data_toggle_q <= '0; // All endpoints
    end else begin
      data_toggle_q <= data_toggle_d;
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_ep_newpkt_o       <= 1'b0;
      out_ep_current_o      <= '0;
      current_xact_setup_q  <= 1'b0;
    end else begin
      if (out_xact_start) begin
        out_ep_newpkt_o      <= 1'b1;
        out_ep_current_o     <= out_ep_current_d;
        current_xact_setup_q <= setup_token_received;
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
      out_ep_data_put_o <= ((out_xact_state == StRcvdDataStart) && rx_data_put_i);
    end
  end

  // nak an OUT if any data comes in with the endpoint full
  // Note that if there is a full size packet buffer this will only be all or nothing
  // but in the case there was a FIFO with less than a max packet size free you
  // could get lucky and the packet received be small and fit with no need to NAK
  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      nak_out_transaction <= 1'b0;
    end else begin
      if ((out_xact_state == StIdle) || (out_xact_state == StRcvdOut)) begin
        nak_out_transaction <= 1'b0;
      end else if (out_ep_data_put_o && out_ep_full_i[out_ep_index]) begin
        nak_out_transaction <= 1'b1;
      end
    end
  end

  // address increment whenever there is a data put unless
  // -- already going to NAK transaction and replay things
  // -- the address is at max packet size
  // NOTE if more than max packet size received then data is lost
  logic increment_addr;
  assign increment_addr = !nak_out_transaction && (~&out_ep_put_addr_o) && out_ep_data_put_o;

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_ep_put_addr_o <= '0;
    end else begin
      if (out_xact_state == StRcvdOut) begin
        out_ep_put_addr_o <= '0;
      end else if ((out_xact_state == StRcvdDataStart) && increment_addr) begin
        out_ep_put_addr_o <= out_ep_put_addr_o + 1;
      end
    end
  end

  ////////////////
  // Assertions //
  ////////////////

endmodule
