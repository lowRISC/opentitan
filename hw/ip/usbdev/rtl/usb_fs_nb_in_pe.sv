// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Copyright Luke Valenty (TinyFPGA project, https://github.com/tinyfpga/TinyFPGA-Bootloader).

// USB Full Speed Non-Buffered Protocol Engine for IN endpoints
//
// Decode IN requests from host and respond with data if there is any
//
// Based on usb_fs_in_pe.v from the TinyFPGA-Bootloader project but
// this version contains no packet buffers

`include "prim_assert.sv"

module usb_fs_nb_in_pe #(
  parameter logic [4:0] NumInEps = 12,
  parameter int unsigned MaxInPktSizeByte = 32,
  // Targeting 17 bit times for the timeout. The counter runs on the 48 MHz
  // clock, the SOP delay to rx_pkt_start_i is 3 bit times, and the EOP delay
  // to tx_pkt_end_i is essentially 0. This timeout originates from Section
  // 7.1.19.1 of the USB 2.0 specification.
  parameter int unsigned AckTimeoutCnt = (17 + 3) * 4,
  localparam int unsigned InEpW = $clog2(NumInEps), // derived parameter
  localparam int unsigned PktW = $clog2(MaxInPktSizeByte), // derived parameter
  localparam int unsigned AckTimeoutCntW = $clog2(AckTimeoutCnt) // derived parameter
) (
  input  logic               clk_48mhz_i,
  input  logic               rst_ni,
  input  logic               link_reset_i,
  input  logic               link_active_i,
  input  logic [6:0]         dev_addr_i,


  ////////////////////
  // endpoint interface
  ////////////////////
  output logic [3:0]            in_ep_current_o, // Other signals addressed to this ep
  output logic                  in_ep_rollback_o, // Bad termination, rollback transaction
  output logic                  in_ep_xact_end_o, // good termination, transaction complete
  output logic [PktW - 1:0]     in_ep_get_addr_o, // Offset requested (0..pktlen)
  output logic                  in_ep_data_get_o, // Accept data (get_addr advances too)
  output logic                  in_ep_newpkt_o, // New IN packet starting (updates in_ep_current_o)
  input  logic [NumInEps-1:0]   in_ep_enabled_i, // Endpoint is enabled and produces handshakes
  input  logic [NumInEps-1:0]   in_ep_stall_i, // Endpoint in a stall state
  input  logic [NumInEps-1:0]   in_ep_has_data_i, // Endpoint has data to supply
  input  logic [7:0]            in_ep_data_i, // Data for current get_addr
  input  logic [NumInEps-1:0]   in_ep_data_done_i, // Set when out of data
  input  logic [NumInEps-1:0]   in_ep_iso_i, // Configure endpoint in isochronous mode

  input  logic [NumInEps-1:0]   data_toggle_clear_i, // Clear the data toggles for an EP

  ////////////////////
  // rx path
  ////////////////////

  // Strobed on reception of packet.
  input  logic              rx_pkt_start_i,
  input  logic              rx_pkt_end_i,
  input  logic              rx_pkt_valid_i,

  // Most recent packet received.
  input  logic [3:0]        rx_pid_i,
  input  logic [6:0]        rx_addr_i,
  input  logic [3:0]        rx_endp_i,

  ////////////////////
  // tx path
  ////////////////////

  // Strobe to send new packet.
  output logic              tx_pkt_start_o,
  input  logic              tx_pkt_end_i,
  // Packet type to send
  output logic [3:0]        tx_pid_o,

  // Data payload to send if any
  output logic              tx_data_avail_o,
  input  logic              tx_data_get_i,
  output logic [7:0]        tx_data_o
);

  ////////////////////////////////////////////////////////////////////////////////
  // in transaction state machine
  ////////////////////////////////////////////////////////////////////////////////

  import usb_consts_pkg::*;

  typedef enum logic [2:0] {
    StIdle,
    StRcvdIn,
    StSendData,
    StWaitTxEnd,
    StWaitAckStart,
    StWaitAck
  } state_in_e;

  state_in_e  in_xact_state;
  state_in_e  in_xact_state_next;

  logic in_xact_end;

  assign in_ep_xact_end_o = in_xact_end;

  // data toggle state
  logic [NumInEps-1:0] data_toggle_q, data_toggle_d;

  // endpoint data buffer
  logic       token_received, setup_token_received, in_token_received, ack_received;
  logic       more_data_to_send;
  logic       ep_in_hw, ep_active;
  logic [3:0] in_ep_current_d;

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

  // Is the specified endpoint actually implemented in hardware?
  assign ep_in_hw = {1'b0, rx_endp_i} < NumInEps;
  assign in_ep_current_d = ep_in_hw ? rx_endp_i : '0;

  // Make widths work - in_ep_current_d/in_ep_current_o only hold implemented endpoint IDs.
  // These signals can be used to index signals of NumInEps width.
  // They are only valid if ep_active is set, i.e., if the specified endpoint is implemented.
  logic [InEpW-1:0] in_ep_index;
  logic [InEpW-1:0] in_ep_index_d;
  assign in_ep_index   = in_ep_current_o[0 +: InEpW];
  assign in_ep_index_d = in_ep_current_d[0 +: InEpW];

  // Is the endpoint active?
  assign ep_active = in_ep_enabled_i[in_ep_index_d] & ep_in_hw;

  assign more_data_to_send =
      in_ep_has_data_i[in_ep_index] & ~in_ep_data_done_i[in_ep_index];

  assign tx_data_avail_o = logic'(in_xact_state == StSendData) & more_data_to_send;

  ////////////////////////////////////////////////////////////////////////////////
  // in transaction state machine
  ////////////////////////////////////////////////////////////////////////////////

  logic [AckTimeoutCntW-1:0] timeout_cntdown_d, timeout_cntdown_q;
  logic rollback_in_xact;

  always_comb begin
    in_xact_state_next = in_xact_state;
    in_xact_end = 1'b0;
    tx_pkt_start_o = 1'b0;
    tx_pid_o = 4'b0000;
    rollback_in_xact = 1'b0;
    timeout_cntdown_d = AckTimeoutCnt[AckTimeoutCntW-1:0];
    unique case (in_xact_state)
      StIdle: begin
        if (ep_active && in_token_received) begin
          in_xact_state_next = StRcvdIn;
        end else begin
          // Ignore tokens to inactive endpoints. Send no response.
          in_xact_state_next = StIdle;
        end
      end

      StRcvdIn: begin
        tx_pkt_start_o = 1'b1; // Need to transmit NAK/STALL or DATA

        if (in_ep_iso_i[in_ep_index]) begin
          // ISO endpoint
          // We always need to transmit. When no data is available, we send
          // a zero-length packet.
          // DATA0 always for full-speed isochronous endpoints
          in_xact_state_next = StSendData;
          tx_pid_o = {UsbPidData0};
        end else if (in_ep_stall_i[in_ep_index]) begin
          in_xact_state_next = StIdle;
          tx_pid_o = {UsbPidStall}; // STALL
        end else if (in_ep_has_data_i[in_ep_index]) begin
          in_xact_state_next = StSendData;
          tx_pid_o = {data_toggle_q[in_ep_index], 1'b0, {UsbPidTypeData}}; // DATA0/1
        end else begin
          in_xact_state_next = StIdle;
          tx_pid_o = {UsbPidNak}; // NAK
        end
      end

      StSendData: begin
        // Use &in_ep_get_addr so width can vary, looking for all ones
        if ((!more_data_to_send) || ((&in_ep_get_addr_o) && tx_data_get_i)) begin
          if (in_ep_iso_i[in_ep_index]) begin
            in_xact_state_next = StIdle; // no ACK for ISO EPs
            in_xact_end = in_ep_has_data_i[in_ep_index];
          end else begin
            if (tx_pkt_end_i) begin
              in_xact_state_next = StWaitAckStart;
            end else begin
              in_xact_state_next = StWaitTxEnd;
            end
          end
        end else begin
          in_xact_state_next = StSendData;
        end
      end

      StWaitTxEnd: begin
        if (tx_pkt_end_i) begin
          in_xact_state_next = StWaitAckStart;
        end
      end

      StWaitAckStart: begin
        // The spec says we have up to 18 bit times to wait for the host
        // response. If it doesn't arrive in time, we must invalidate the
        // transaction.
        timeout_cntdown_d = timeout_cntdown_q - 1'b1;

        if (rx_pkt_start_i) begin
          in_xact_state_next = StWaitAck;
        end else if (timeout_cntdown_q == '0) begin
          in_xact_state_next = StIdle;
          rollback_in_xact = 1'b1;
        end else begin
          in_xact_state_next = StWaitAckStart;
        end
      end

      StWaitAck: begin
        if (ack_received) begin
          in_xact_state_next = StIdle;
          in_xact_end = 1'b1;
        end else if (in_token_received) begin
          in_xact_state_next = StRcvdIn;
          rollback_in_xact = 1'b1;
        end else if (rx_pkt_end_i) begin
          in_xact_state_next = StIdle;
          rollback_in_xact = 1'b1;
        end else begin
          in_xact_state_next = StWaitAck;
        end
      end

      default: in_xact_state_next = StIdle;
    endcase
  end

  `ASSERT(InXactStateValid_A,
    in_xact_state inside {StIdle, StRcvdIn, StSendData, StWaitTxEnd, StWaitAckStart, StWaitAck},
    clk_48mhz_i)

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      timeout_cntdown_q <= AckTimeoutCnt[AckTimeoutCntW-1:0];
    end else begin
      timeout_cntdown_q <= timeout_cntdown_d;
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      tx_data_o <= '0;
    end else begin
      tx_data_o <= in_ep_data_i;
    end

  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      in_xact_state <= StIdle;
      in_ep_rollback_o <= 1'b0;
    end else if (link_reset_i || !link_active_i) begin
      in_xact_state <= StIdle;
      in_ep_rollback_o <= 1'b0;
    end else begin
      in_xact_state <= in_xact_state_next;
      in_ep_rollback_o <= rollback_in_xact;
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      in_ep_get_addr_o <= '0;
    end else begin
      if (in_xact_state == StIdle) begin
        in_ep_get_addr_o <= '0;
      end else if ((in_xact_state == StSendData) && tx_data_get_i) begin
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
        in_ep_current_o <= in_ep_current_d;
        in_ep_newpkt_o <= 1'b1;
      end else begin
        in_ep_newpkt_o <= 1'b0;
      end
    end
  end

  always_comb begin : proc_data_toggle_d
    data_toggle_d = data_toggle_q;

    if (setup_token_received && ep_active) begin
      data_toggle_d[in_ep_index_d] = 1'b1;
    end else if ((in_xact_state == StWaitAck) && ack_received) begin
      data_toggle_d[in_ep_index] = ~data_toggle_q[in_ep_index];
    end

    data_toggle_d = data_toggle_d & ~data_toggle_clear_i;
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_toggle_q <= '0; // Clear for all endpoints
    end else if (link_reset_i) begin
      data_toggle_q <= '0; // Clear for all endpoints
    end else begin
      data_toggle_q <= data_toggle_d;
    end
  end

  always_ff @(posedge clk_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      in_ep_data_get_o <= 1'b0;
    end else begin
      if ((in_xact_state == StSendData) && tx_data_get_i) begin
        in_ep_data_get_o <= 1'b1;
      end else begin
        in_ep_data_get_o <= 1'b0;
      end
    end
  end

  ////////////////
  // Assertions //
  ////////////////

endmodule
