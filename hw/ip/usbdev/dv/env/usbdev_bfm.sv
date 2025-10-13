// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Bus Functional Model of USBDEV.
class usbdev_bfm extends uvm_component;
  `uvm_component_utils(usbdev_bfm)

  // Number of bits required to represent the number of bytes within a buffer.
  localparam int unsigned BufSizeW = $clog2(MaxPktSizeByte + 1);

  // No valid IN transaction is indicated by setting `tx_ep` to this value.
  localparam bit [3:0] InvalidEP = 4'hF;

  //------------------------------------------------------------------------------------------------
  // Type definitions.
  //------------------------------------------------------------------------------------------------
  typedef bit [5:0] buf_num;

  // Details of RX FIFO entry.
  typedef struct
  {
    buf_num            buffer;
    bit          [3:0] ep;
    bit                setup;
    bit [BufSizeW-1:0] size;
  } rxfifo_entry_t;

  // State of IN endpoint and any packet awaiting collection.
  typedef struct {
    buf_num            buffer;
    bit [BufSizeW-1:0] size;
    bit                sending;
    bit                pend;
    bit                rdy;
  } configin_t;

  // Status of AON/Wake functionality.
  typedef struct {
    bit bus_not_idle;
    bit bus_reset;
    bit disconnected;
    bit module_active;
  } wake_events_t;

  // Are we in a 'powered' state?
  // Note: presently we do not model power down/reset fully, but this flag determines
  // whether USB events are visible/monitored even when the aon_wake module is active.
  bit powered;

  // Current interrupt state; exact CSR mimics, may be updated directly.
  bit [31:0] intr_test;
  bit [31:0] intr_state;
  bit [31:0] intr_enable;

  // Control and status.
  bit enable; // Pullup enable (indicate device presence on the USB).
  bit [6:0] dev_address; // Assigned device address.
  bit [10:0] frame; // Most recent frame number.

  // Connection state.
  bit host_lost;  // Non-idle but no SOF detected for > 4ms.
  usbdev_link_state_e link_state; // Current state of link.
  bit sense;  // VBUS/SENSE signal from host/hub.

  // Current endpoint configuration; exact CSR mimics, may be updated directly.
  bit [NEndpoints-1:0] ep_out_enable;
  bit [NEndpoints-1:0] ep_in_enable;
  bit [NEndpoints-1:0] rxenable_setup;
  bit [NEndpoints-1:0] rxenable_out;
  bit [NEndpoints-1:0] set_nak_out;
  bit [NEndpoints-1:0] out_stall;
  bit [NEndpoints-1:0] in_stall;
  bit [NEndpoints-1:0] out_iso;
  bit [NEndpoints-1:0] in_iso;

  // Current reception (SETUP and OUT) state information.
  token_pkt rx_token; // Most recent OUT-side token packet.
  bit [3:0] rx_ep;    // Retain the endpoint for the handshake packet.
  // Current transmission (IN) state information.
  bit [3:0] tx_ep;

  // Sent IN packets; may be _read_ directly. Use 'write_in_sent' to modify it.
  bit [NEndpoints-1:0] in_sent;

  // Current IN configuration.
  configin_t configin[NEndpoints];

  // Data Toggle bits; current state of toggles may be _read_ directly.
  // Use 'write_in|out_toggles' functions to modify them.
  bit [NEndpoints-1:0] in_toggles;
  bit [NEndpoints-1:0] out_toggles;

  // Available OUT and SETUP Buffer FIFOs.
  buf_num avout_fifo[$];
  buf_num avsetup_fifo[$];

  // RX FIFO.
  rxfifo_entry_t rx_fifo[$];

  // AON/Wake status.
  wake_events_t wake_events;

  // Internal packet buffer memory; this is a 32-bit addressable read/write memory accessed from
  // both the CSR and USB sides. It is, however, decomposed into 'NumBuffers' packet-sized buffers
  // of 'MaxPktSizeByte' bytes each, with each packet buffer serving only as a unidirectional
  // channel (IN packet or OUT packet), and is not required to support simultaneous reads and writes
  // to any given packet buffer.
  logic [31:0] buffer[NumBuffers * MaxPktSizeByte / 4];

  // The DUT and BFM packet buffer memories are 32 bits wide (TL-UL interface) and only full 32-bit
  // reads and writes are possible, but the packet data from the USB has byte-level granularity.
  //
  // This means that the final word of each packet read from the buffer memories could mismatch
  // if nothing guaranteed that the unused bytes are the same. Here we mimic what happens internally
  // within the DUT; a bank of 32 flops is cleared by the IP block reset, and individual bytes
  // within this bank are replaced when actual bytes are received from the USB. (usbdev_usbif.sv)
  bit [31:0] wdata_q;

  // The decision on whether and how to respond to an IN request cannot be actioned immediately
  // because the CSR state may change in the interim; we introduce a short delay before deciding
  // how to respond to an IN request.
  token_pkt in_token;

  // Count of elapsed DUT clock ticks whilst timing (currently just for servicing IN requests).
  int unsigned tick_cnt = 0;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    dut_reset();
    // Initialize AON/Wake state.
    wake_events.bus_not_idle  = 1'b0;
    wake_events.bus_reset     = 1'b0;
    wake_events.disconnected  = 1'b0;
    wake_events.module_active = 1'b0;
  endfunction

  // Reset assertion to the DUT; this is a reset of the IP block; not a Bus Reset on the USB.
  function void dut_reset();
    configin_t configin_rst;  // Defaults to zeros throughout.
    `uvm_info(`gfn, "Modeling DUT reset", UVM_LOW)
    powered = 1'b1;
    // Assigned device address is discarded and the DUT returns to the disconnected state.
    dev_address = 0;
    enable = 0;
    link_state = LinkDisconnected;
    host_lost = 1'b0;
    frame = 0;
    // Data Toggle bits are all cleared.
    out_toggles = 0;
    in_toggles = 0;
    in_sent = 0;
    // Endpoint configuration is reset.
    ep_out_enable = 0;
    ep_in_enable = 0;
    rxenable_setup = 0;
    rxenable_out = 0;
    set_nak_out = 0;
    out_stall = 0;
    in_stall = 0;
    out_iso = 0;
    in_iso = 0;
    // Most of the interrupt lines are deasserted.
    intr_state = 0;
    intr_state[IntrDisconnected] = 1'b1; // Held in 'Disconnected' state during IP reset.
    intr_enable = 0;
    intr_test = 0;
    // Empty the FIFOs.
    avout_fifo.delete();
    avsetup_fifo.delete();
    rx_fifo.delete();
    // Note: packet buffer contents are unmodified by DUT reset, but the bank of 32 flops is reset.
    wdata_q <= 32'b0;
    // Note: AON/Wake state also unaffected.
    // Note: `sense` line is unaffected; it's an external input to the DUT.
    // Record that there is no IN transmission configured or in progress.
    for (int unsigned ep = 0; ep < NEndpoints; ep++) configin[ep] = configin_rst;
    tx_ep = InvalidEP;
    // Nor any in-progress reception.
    rx_ep = InvalidEP;
    rx_token = null;
  endfunction

  //------------------------------------------------------------------------------------------------
  // Timing model.
  //------------------------------------------------------------------------------------------------

  // Returns 1 iff there is a need to track the passage of time in clock ticks; caller shall invoke
  // `send_delayed_response()` once per clock cycle of the DUT whilst this is the case.
  function bit timing();
    return (in_token != null);
  endfunction

  // Advance by one clock tick and action any timed response that is now due; returns an indication
  // of whether a response is expected from the DUT, and the response itself via 'rsp'.
  function bit send_delayed_response(output usb20_item rsp);
    bit send_rsp = 1'b0;
    tick_cnt++;
    `uvm_info(`gfn, $sformatf("BFM advanced tick count to 0x%0x", tick_cnt), UVM_MEDIUM)
    if (tick_cnt >= 2 && in_token != null) begin
      // Decide how to respond to the IN token packet.
      rsp = in_packet(in_token);
      send_rsp = 1'b1;
      // Forget the IN request.
      in_token = null;
    end
    return send_rsp;
  endfunction

  //------------------------------------------------------------------------------------------------
  // CSR-side endpoint operations.
  //------------------------------------------------------------------------------------------------
  function void write_in_sent(bit [NEndpoints-1:0] mask);
    in_sent &= ~mask;
    if (~|in_sent) intr_state[IntrPktSent] = 1'b0; // Deassert Status interrupt.
  endfunction

  //------------------------------------------------------------------------------------------------
  // CSR-side Data Toggle operations.
  //------------------------------------------------------------------------------------------------
  function void write_out_toggles(bit [NEndpoints-1:0] mask, bit [NEndpoints-1:0] status);
    out_toggles = (out_toggles & ~mask) | (status & mask);
  endfunction

  function void write_in_toggles(bit [NEndpoints-1:0] mask, bit [NEndpoints-1:0] status);
    in_toggles = (in_toggles & ~mask) | (status & mask);
  endfunction

  //------------------------------------------------------------------------------------------------
  // CSR-side FIFO operations.
  //------------------------------------------------------------------------------------------------
  function void avsetup_fifo_add(buf_num b);
    if (avsetup_fifo.size() < AvSetupFIFODepth) begin
      avsetup_fifo.push_back(b);
      intr_state[IntrAvSetupEmpty] = 1'b0; // Deassert Status interrupt.
    end else intr_state[IntrAvOverflow] = 1'b1;
  endfunction

  function void avout_fifo_add(buf_num b);
    if (avout_fifo.size() < AvOutFIFODepth) begin
      avout_fifo.push_back(b);
      intr_state[IntrAvOutEmpty] = 1'b0; // Deassert Status interrupt.
    end else intr_state[IntrAvOverflow] = 1'b1;
  endfunction

  function bit rx_fifo_read(output rxfifo_entry_t entry);
    if (rx_fifo.size() > 0) begin
      entry = rx_fifo.pop_front();
      // Deassert Status interrupts.
      intr_state[IntrRxFull] = 1'b0;
      if (!rx_fifo.size()) intr_state[IntrPktReceived] = 1'b0;
      return 1;
    end
    // No FIFO entry available.
    return 0;
  endfunction

  function void avout_fifo_rst();
    avout_fifo.delete();
    // Status interrupt is asserted only if device connection enabled.
    intr_state[IntrAvOutEmpty] = enable;
  endfunction

  function void avsetup_fifo_rst();
    avsetup_fifo.delete();
    // Status interrupt is asserted only if device connection enabled.
    intr_state[IntrAvSetupEmpty] = enable;
  endfunction

  function void rx_fifo_rst();
    rx_fifo.delete();
    // Deassert Status interrupts.
    intr_state[IntrRxFull] = 1'b0;
    intr_state[IntrPktReceived] = 1'b0;
  endfunction

  //------------------------------------------------------------------------------------------------
  // CSR-side packet buffer operations.
  //------------------------------------------------------------------------------------------------
  // Write a 32-bit word into the packet buffer memory; address offset is in 32-bit words.
  function void write_buffer(int unsigned offset, logic [31:0] d);
    buffer[offset] = d;
  endfunction

  // Read a 32-bit word from the packet buffer memory; address offset is in 32-bit words.
  function logic [31:0] read_buffer(int unsigned offset);
    return buffer[offset];
  endfunction

  //------------------------------------------------------------------------------------------------
  // Link state changes.
  //------------------------------------------------------------------------------------------------
  function void set_enable(bit en);
    // Retain the state of the pullup enable; transition into the Powered link state occurs only in
    // the presence of both VBUS/SENSE and the pullup enable.
    enable = en;
    if (en) begin
      if (link_state == LinkDisconnected && sense) begin
        link_state = LinkPowered;
        intr_state[IntrPowered] = 1'b1;
      end
      // The FIFO empty Status interrupts are not asserted until we connect.
      if (!avsetup_fifo.size()) intr_state[IntrAvSetupEmpty] = 1'b1;
      if (!avout_fifo.size())   intr_state[IntrAvOutEmpty]   = 1'b1;
    end else begin
      dev_address = 0;
      link_state = LinkDisconnected;
      intr_state[IntrDisconnected] = 1'b1;
      // The FIFO empty Status interrupts are only asserted whilst `enable` is asserted.
      intr_state[IntrAvSetupEmpty] = 1'b0;
      intr_state[IntrAvOutEmpty]   = 1'b0;
    end
  endfunction

  // Software-initiated resume from a power-up, suspended state (return from Deep Sleep).
  function void resume_link_active();
    if (link_state == LinkPowered) begin
      link_state = LinkResuming;
    end
  endfunction

  //------------------------------------------------------------------------------------------------
  // AON/Wake functionality.
  //------------------------------------------------------------------------------------------------
  function void set_wake_control(bit suspend_req, bit wake_ack);
    if (wake_events.module_active & wake_ack) begin
      // Deactivate the monitoring; leave the event report(s) asserted.
      wake_events.module_active = 1'b0;
    end else if (!wake_events.module_active & suspend_req) begin
      // Activate the AON/Wake monitoring of the USB.
      wake_events.bus_not_idle  = 1'b0;
      wake_events.bus_reset     = 1'b0;
      wake_events.disconnected  = 1'b0;
      wake_events.module_active = 1'b1;
    end
  endfunction

  //------------------------------------------------------------------------------------------------
  // USB-side bus events.
  //------------------------------------------------------------------------------------------------
  // Bus Reset from host/hub.
  function void bus_reset(bit completed = 1'b1);
    out_toggles = 0;
    in_toggles = 0;
    if (wake_events.module_active) begin
      wake_events.bus_reset = 1'b1;
      // 'Bus not idle' indication is also asserted when a Bus Reset occurs, since SE0 is a
      // non-idle state.
      wake_events.bus_not_idle = 1'b1;
    end
    if (powered) begin
      dev_address = 0;
      intr_state[IntrLinkReset] = 1'b1;
      // Link reset cancels all IN packets that are awaiting collection, clearing 'rdy' and
      // 'sending' and setting the 'pend' bit.
      for (int unsigned ep = 0; ep < NEndpoints; ep++) retire_in_packet(ep);
      tx_ep = InvalidEP;
      // Discard any memory of a token packet from before the Reset Signaling.
      rx_token = null;
    end
    // Link state changes occur only when the Reset Signaling is complete.
    if (powered && sense && enable) begin
      if (completed) begin
        link_state = LinkActiveNoSOF;
        if (link_state == LinkSuspended || link_state == LinkResuming) begin
          // Bus Reset also implies the end of Suspend/Resume Signaling.
          intr_state[IntrLinkResume] = 1'b1;
        end
      end else begin
        // The DUT detects Bus Reset as 'non-Idle' too.
        if (link_state == LinkPoweredSuspended || link_state == LinkSuspended) begin
          link_state = (link_state == LinkPoweredSuspended) ? LinkPowered : LinkResuming;
          intr_state[IntrLinkResume] = 1'b1;
        end
      end
    end
  endfunction

  // Suspend signaling detected; over 3ms have elapsed in the Idle state.
  function void bus_suspend();
    link_state = (link_state == LinkPowered) ? LinkPoweredSuspended : LinkSuspended;
    intr_state[IntrLinkSuspend] = 1'b1;
  endfunction

  // Resume Signaling detected.
  function void bus_resume(bit completed = 1'b1);
    if (wake_events.module_active) wake_events.bus_not_idle = 1'b1;
    if (powered) begin
      if (completed) begin
        if (link_state == LinkResuming) link_state = LinkActiveNoSOF;
        intr_state[IntrLinkResume] = 1'b1;
      end else begin
        case (link_state)
          LinkSuspended: link_state = LinkResuming;
          LinkPoweredSuspended: begin
            link_state = LinkPowered;
            intr_state[IntrLinkResume] = 1'b1;
          end
          default: begin
            // Nothing to be done.
          end
        endcase
      end
    end
  endfunction

  // VBUS/SENSE connection event.
  function void bus_connect();
    sense = 1'b1;
    if (powered) begin
      // The 'powered' link state reflects VBUS assertion with pullup enabled.
      if (enable) link_state = LinkPowered;
      // An interrupt is raised when VBUS becomes asserted, irrespective of the pullup state.
      intr_state[IntrPowered] = 1'b1;
    end
  endfunction

  // VBUS/SENSE disconnection event.
  function void bus_disconnect();
    sense = 1'b0;
    if (wake_events.module_active) wake_events.disconnected = 1'b1;
    if (powered) begin
      link_state = LinkDisconnected;
      intr_state[IntrDisconnected] = 1'b1;
      dev_address = 0;
    end
  endfunction

  //------------------------------------------------------------------------------------------------
  // USB-side packet operations.
  //------------------------------------------------------------------------------------------------
  //
  // Some malformed packets shall be ignored entirely by the DUT:
  // - invalid sync field, invalid length, invalid EOP.
  //
  // Those which have valid packet framing may still contain errors, which shall be reported
  // diagnostically, but the packet shall be ignored:
  // - invalid PID, bit stuffing errors, CRC mismatches.
  //
  // The expectation is that bit stuffing violations shall yield CRC errors too, since the intended
  // data is now undetermined.

  // Cancel any in-progress IN transaction and update state.
  function void cancel_in();
    // Forget any IN request about which we have not made a decision.
    in_token = null;
    // Was there an IN transmission in progress?
    if (tx_ep != InvalidEP) begin
      configin[tx_ep].sending = 1'b0;
      intr_state[IntrLinkInErr] = 1'b1;
      tx_ep = InvalidEP;
    end
  endfunction

  // Cancel any in-progress OUT transaction and update state.
  function void cancel_out();
    rx_ep = InvalidEP;
    if (rx_token != null) begin
      intr_state[IntrLinkOutErr] = 1'b1;
      rx_token = null;
    end
  endfunction

  // Cancel any in-progress IN or OUT transaction and update state.
  function void cancel_transaction();
    cancel_in();
    cancel_out();
  endfunction

  // Retire any IN packet on the given endpoint, marking it as 'pend'ing not 'rdy.'
  function void retire_in_packet(bit [3:0] ep);
    if (configin[ep].rdy) begin
      configin[ep].rdy  = 1'b0;
      configin[ep].pend = 1'b1;
    end
    configin[ep].sending = 1'b0;
  endfunction

  // Returns an indication of whether this packet is accepted as valid, and update internal state
  // according to any errors detected.
  function bit valid_packet(usb20_item item);
    if (!item.valid_pid()) intr_state[IntrRxPidErr] = 1'b1;
    if (!item.valid_stuffing) begin
      bit exp_crc_error = 1;
      intr_state[IntrRxBitstuffErr] = 1'b1;
      // The expectation is that a bit stuffing violation will also induce a CRC error, except in
      // the very specific case of us having generated a violation right at the end of a token
      // packet.
      if (item.m_pkt_type == PktTypeToken) begin
        token_pkt tok;
        `downcast(tok, item.clone());
        exp_crc_error = tok.crc5 != 5'h1f || tok.endpoint[3:2] != 2'b11;
      end
      if (exp_crc_error) intr_state[IntrRxCrcErr] = 1'b1;
    end
    if (!item.valid_crc()) intr_state[IntrRxCrcErr] = 1'b1;
    // The expectation is that an invalid length/EOP will also induce a CRC error if it's known to
    // be a token or data packet.
    if ((item.m_pkt_type == PktTypeToken || item.m_pkt_type == PktTypeData) &&
        (!item.valid_length || !item.valid_eop)) begin
      intr_state[IntrRxCrcErr] = 1'b1;
    end
    return &{item.valid_pid(), item.valid_length, item.valid_stuffing, item.valid_crc(),
             item.valid_eop};
  endfunction

  // Complete an in-progress Isochronous IN transaction.
  function void in_iso_completed(bit [3:0] ep);
    // Check that there is a pending IN transaction.
    assert(ep != InvalidEP && ep < NEndpoints);
    assert(in_iso[ep] & !rxenable_setup[ep]);
    if (configin[ep].rdy) begin
      in_sent[ep] = 1'b1;
      intr_state[IntrPktSent] = 1'b1;
    end
    // Update the IN configuration.
    configin[ep].sending = 1'b0;
    configin[ep].rdy = 1'b0;
  endfunction

  // Process a Start of Frame packet from the USB host controller.
  function void sof_packet(ref sof_pkt sof);
    cancel_transaction();
    if (!(sof.valid_sync)) return;
    void'(valid_packet(sof)); // Ensure errors are reported.
    if (sof.valid_pid()) begin
      // The frame number itself shall be used only if the CRC matches.
      if (&{sof.valid_length, sof.valid_stuffing, sof.valid_crc()}) frame = sof.framenum;
      // SOF packets with invalid CRC still affect the link state.
      link_state = LinkActive;
      intr_state[IntrFrame] = 1'b1;
    end else intr_state[IntrRxPidErr] = 1'b1;
  endfunction

  // Process a token packet from the USB host controller.
  function bit token_packet(ref token_pkt token, output usb20_item rsp);
    cancel_transaction();
    if (|{token.low_speed, !token.valid_sync}) return 0;
    if (valid_packet(token)) begin
      case (token.m_pid_type)
        PidTypeSetupToken, PidTypeOutToken: begin
          bit [3:0] ep = token.endpoint;
          // Basic check of whether we should do anything at all for this transaction.
          if (token.address != dev_address || ep >= NEndpoints) return 0;
          // SETUP token has immediate consequence for the DUT state; both SETUP and OUT token
          // packets cause some state information to be retained so that the ensuing DATA packet may
          // be processed.
          if (token.m_pid_type == PidTypeSetupToken) begin
            // Detection of a SETUP, whether or not it's stored clears the Data Toggles bits, iff
            // the endpoints are enabled.
            if (ep_out_enable[ep]) out_toggles[ep] = 1'b0;
            if (ep_in_enable[ep])  in_toggles[ep]  = 1'b1;
          end
          if (!ep_out_enable[ep]) return 0;  // Silently ignored.
          `downcast(rx_token, token.clone())
          // Nothing more to do until the DATA packet is received; `rx_token` holds the required
          // state.
        end
        PidTypeInToken: begin
          // Basic check of whether we should do anything at all for this transaction.
          bit [3:0] ep = token.endpoint;
          if (token.address != dev_address || ep >= NEndpoints || !ep_in_enable[ep]) return 0;

          // Remember the IN token packet and, after a short delay, decide whether and how to
          // respond.
          `downcast(in_token, token.clone());
          tick_cnt = 0;
        end
        default: begin
          // DUT shall ignore all other token packets; not relevant to Full Speed devices.
          `uvm_info(`gfn, $sformatf("Ignoring unexpected token 0%0x", token.m_pid_type), UVM_LOW)
        end
      endcase
    end
    return 0;
  endfunction

  // Process receipt of a DATA packet from the USB host controller; returns an indication of
  // whether a response packet is expected, and the response itself via `rsp`.
  // OUT DATA packets yield a response that is 'stall', 'ack' or 'nak.'
  function bit data_packet(ref data_pkt data, output usb20_item rsp);
    bit valid_crc = data.valid_crc();
    cancel_in();
    if (|{data.low_speed, !data.valid_sync}) return 0;
    if (valid_packet(data) && (data.m_pid_type == PidTypeData0 ||
                               data.m_pid_type == PidTypeData1)) begin
      // Consult the most recent token packet to decide how to handle the DATA packet.
      if (rx_token == null || (rx_token.m_pid_type != PidTypeSetupToken &&
                               rx_token.m_pid_type != PidTypeOutToken)) begin
        // DUT shall ignore any DATA packet without a preceding SETUP/OUT packet; likely a result
        // of data loss.
        `uvm_info(`gfn, $sformatf("Ignoring orphaned DATA packet 0x%0x", data.m_pid_type),
                  UVM_LOW)
      end else begin
        // Process the most recent SETUP/OUT packet and DATA packet together.
        return out_packet(rx_token, data, rsp);
      end
    end else begin
      // A SETUP packet that would not be received does not result in a LinkOutErr if the DATA
      // packet is invalid because the OUT Packet Engine does not start accepting it.
      if (rx_token != null && rx_token.m_pid_type == PidTypeSetupToken &&
          !rxenable_setup[rx_token.endpoint]) begin
        rx_token = null;
      end else cancel_out();
    end
    return 0;
  endfunction

  // Process an IN transaction from the USB host controller; returns an expectation of the DUT
  // response packet. The response may be 'stall', 'data' or 'nak.'
  function usb20_item in_packet(ref token_pkt token);
    usb20_item rsp;
    bit [3:0] ep;

    // Validate inputs.
    assert(token.m_ev_type  == EvPacket);
    assert(token.m_pkt_type == PktTypeToken);
    ep = token.endpoint;

    if (in_stall[ep] & (!in_iso[ep] | rxenable_setup[ep])) begin
      usb20_item stall = handshake_pkt::type_id::create("stall");
      stall.m_pid_type = PidTypeStall;
      // Return STALL response.
      rsp = stall;
    end else begin
      // Control takes precedence over Isochronous setting in the event of such a misconfiguration.
      bit iso_in_endpoint = in_iso[ep] & !rxenable_setup[ep];
      // What about the IN configuration for this endpoint?
      bit rdy = configin[ep].rdy;
      if (rdy || iso_in_endpoint) begin
        data_pkt data;
        configin[ep].sending = 1'b1;

        data = data_pkt::type_id::create("data");
        if (iso_in_endpoint) begin
          // Isochronous transactions receive no handshake packet so we're already done, but
          // the packet sent signaling occurs only if there was a pending IN packet.
          in_iso_completed(ep);
          // Always use DATA0 for Full Speed Isochronous transactions.
          data.m_pid_type = PidTypeData0;
          // Forget any IN request about which we have not made a decision.
          in_token = null;
          tx_ep = InvalidEP;
        end else begin
          // Remember the endpoint involved in the IN transmission so that the handshake response
          // may be handled appropriately.
          tx_ep = ep;
          data.m_pid_type = in_toggles[ep] ? PidTypeData1 : PidTypeData0;
        end
        // Isochronous endpoints send a Zero Length Packet if there is no IN packet pending.
        if (rdy) read_pkt_bytes(configin[ep].buffer, configin[ep].size, data.data);
        data.crc16 = data.exp_crc();
        rsp = data;
      end else begin
        usb20_item nak = handshake_pkt::type_id::create("nak");
        nak.m_pid_type = PidTypeNak;
        // Return NAK response.
        rsp = nak;
      end
    end
    return rsp;
  endfunction

  // Process a handshake packet, in response to an attempted transaction to the given endpoint.
  function void handshake_packet(ref handshake_pkt handshake);
    cancel_out();
    if (|{handshake.low_speed, !handshake.valid_sync}) return;
    if (!handshake.valid_pid()) intr_state[IntrRxPidErr] = 1'b1;
    if (tx_ep < NEndpoints) begin
      case (handshake.m_pid_type)
        PidTypeAck: begin
          // Update the Data Toggle bit.
          in_toggles[tx_ep] ^= 1'b1;
          // Update the IN configuration.
          configin[tx_ep].sending = 1'b0;
          configin[tx_ep].rdy = 1'b0;
          in_sent[tx_ep] = 1'b1;
          intr_state[IntrPktSent] = 1'b1;
        end
        PidTypeNak: begin
          configin[tx_ep].sending = 1'b0;
          intr_state[IntrLinkInErr] = 1'b1;
        end
        // Any other response is unexpected.
        default: begin
          configin[tx_ep].sending = 1'b0;
          intr_state[IntrLinkInErr] = 1'b1;
        end
      endcase
      // IN transmission completed.
      tx_ep = InvalidEP;
    end
  endfunction

  // Process the receipt of an OUT DATA or SETUP DATA packet, returning an indication of whether
  // a response was produced on the USB. The responses will be one of 'stall', 'ack' or 'nak.'
  function bit out_packet(ref token_pkt token, ref data_pkt data, output usb20_item rsp);
    rxfifo_entry_t e;
    bit bad_toggle;
    usb20_item ack;
    bit [3:0] ep;

    // Validate inputs.
    assert(token.m_ev_type  == EvPacket);
    assert(data.m_ev_type   == EvPacket);
    assert(token.m_pkt_type == PktTypeToken);
    assert(data.m_pkt_type  == PktTypeData);

    // First we concern ourselves with the packet type-dependent impact upon the hardware state.
    ep = token.endpoint;
    case (token.m_pid_type)
      PidTypeSetupToken: begin
        bit avsetup_empty = !avsetup_fifo.size();
        // Silently ignore SETUP packets to endpoints not configured to receive them.
        if (!rxenable_setup[ep]) begin
          rx_ep = InvalidEP;
          rx_token = null;
          return 0;
        end
        // Collect the packet contents into the buffer, if one is available, as well as updating
        // the internal `wdata` flops.
        write_pkt_bytes(!avsetup_empty, avsetup_empty ? 0 : avsetup_fifo[0], data);
        if (avsetup_empty || rx_fifo.size() >= RxFIFODepth) begin
          // SETUP packets that cannot be accepted are just ignored.
          cancel_out();
          return 0;
        end
        bad_toggle = out_toggles[ep] ^ (data.m_pid_type != PidTypeData0);
        if (!bad_toggle) begin
          e.buffer = avsetup_fifo.pop_front();
          e.setup = 1;
          if (!avsetup_fifo.size()) intr_state[IntrAvSetupEmpty] = 1;
          // A SETUP packet successfully received also clears the stall conditions.
          out_stall[ep] = 1'b0;
          in_stall[ep]  = 1'b0;
          // It also retires any ready IN packet on that endpoint.
          retire_in_packet(ep);
        end
      end

      PidTypeOutToken: begin
        bit avout_empty = !avout_fifo.size();
        // Collect the packet contents into the buffer, if one is available, as well as updating
        // the internal `wdata` flops.
        write_pkt_bytes(!avout_empty, avout_empty ? 0 : avout_fifo[0], data);
        // Is the OUT endpoint stalled? This has priority over other reasons for rejection, but does
        // not apply to Isochronous endpoints (no handshake responses) unless they're also set to
        // receive SETUP packets (misconfigured).
        if (out_stall[ep] & (!out_iso[ep] | rxenable_setup[ep])) begin
          usb20_item stall = handshake_pkt::type_id::create("stall");
          stall.m_pid_type = PidTypeStall;
          cancel_out();
          // Response is STALL.
          rsp = stall;
          return 1;
        end
        // Note: the final entry of the RX FIFO is reserved solely for SETUP packets.
        if (avout_empty || rx_fifo.size() >= RxFIFODepth - 1 || !rxenable_out[ep]) begin
          usb20_item nak;
          cancel_out();
          // Construct a NAK response indicating that we're busy, unless Isochronous. If an endpoint
          // is misconfigured to be both Control and Isochronous, Control wins.
          if (out_iso[ep] & !rxenable_setup[ep]) return 0;
          // Retain the endpoint number for subsequent processing of the DUT handshake response.
          rx_ep = ep;
          nak = handshake_pkt::type_id::create("nak");
          nak.m_pid_type = PidTypeNak;
          // NAK response.
          rsp = nak;
          return 1;
        end
        // A packet shall be ACKnowledged even if the Data Toggle bit is not as expected, because
        // that is taken to imply the loss of our previous ACKnowledgement and that the host is
        // resending.
        //
        // We store and record the packet only if the toggle bit is as expected, however.
        bad_toggle = !out_iso[ep] & (out_toggles[ep] ^ (data.m_pid_type != PidTypeData0));
        if (!bad_toggle) begin
          e.buffer = avout_fifo.pop_front();
          e.setup = 0;
          if (!avout_fifo.size()) intr_state[IntrAvOutEmpty] = 1'b1;
        end
      end
      default: `uvm_fatal(`gfn, $sformatf("Unexpected PID type 0x%x", token.m_pid_type))
    endcase

    // At this point we have committed ourselves on whether to receive or drop the packet.
    if (bad_toggle) begin
      intr_state[IntrLinkOutErr] = 1'b1;
    end else begin
      // Update the Data Toggle bit.
      out_toggles[ep] ^= 1'b1;
      // Complete the packet description and add it to the RX FIFO.
      e.ep = ep;
      e.size = data.data.size();
      rx_fifo.push_back(e);
      // 'Set NAK on OUT' functionality; accepts a single OUT packet at a time on the endpoint,
      // gated by software control.
      if (set_nak_out[ep]) rxenable_out[ep] = 1'b0;
      // Packet received.
      intr_state[IntrRxFull] = (rx_fifo.size() >= RxFIFODepth);
      intr_state[IntrPktReceived] = 1'b1;
    end

    // Retain the endpoint number for subsequent processing of the DUT handshake response.
    rx_ep = ep;
    // Now forget the OUT transaction; successfully completed.
    rx_token = null;
    // Isochronous transactions do not include a handshake packet, but 'control endpoints' take
    // precedence; it is a configuration error to have an Isochronous Control endpoint, however.
    if (out_iso[ep] & !rxenable_setup[ep]) return 0;

    ack = handshake_pkt::type_id::create("ack");
    ack.m_pid_type = PidTypeAck;
    // ACKnowledge.
    rsp = ack;
    return 1;
  endfunction

  // Internal function to write the bytes of a SETUP/OUT DATA packet into the specified buffer,
  // if a buffer is available, as well as updating the internal `wdata` flops.
  function void write_pkt_bytes(bit buf_avail, int unsigned buffer, ref data_pkt data);
    int unsigned buf_start = (buffer * MaxPktSizeByte) >> 2;
    byte unsigned wr_data[$];
    int unsigned wr_bytes;
    // The DUT actually writes the CRC16 bytes into the packet buffer too, if they fit, because
    // it does not know until the EOP signaling that they _are_ the CRC16 bytes. EOP marks the end
    // of the bitstream.
    wr_data = data.data;
    wr_data.push_back(data.crc16[7:0]);
    wr_data.push_back(data.crc16[15:8]);
    wr_bytes = data.data.size() + 2;
    // Collect bytes, writing full words into the packet buffer memory but not over-running the
    // packet buffer. However, additional bytes are still remembered in the flops and may be written
    // into packet buffers by subsequent short transfers.
    for (int unsigned offset = 0; offset < wr_bytes; offset++) begin
      // DUT stops incrementing its write offset at the end of the packet buffer, but still keeps
      // replacing the final byte within the flops.
      int unsigned wr_offset = (offset >= MaxPktSizeByte) ? (MaxPktSizeByte - 1) : offset;
      case (wr_offset & 3)
        0:       wdata_q[7:0]   = wr_data[offset];
        1:       wdata_q[15:8]  = wr_data[offset];
        2:       wdata_q[23:16] = wr_data[offset];
        default: wdata_q[31:24] = wr_data[offset];
      endcase
      if (buf_avail && offset < MaxPktSizeByte &&
          (((offset & 3) == 3) || (offset >= wr_bytes - 1))) begin
        write_buffer(buf_start + (offset >> 2), wdata_q);
      end
    end
  endfunction

  // Internal function to read the bytes of an IN DATA packet from the specified buffer.
  function void read_pkt_bytes(int unsigned buffer, int unsigned pkt_len,
                               output byte unsigned data[]);
    int unsigned buf_start = (buffer * MaxPktSizeByte) >> 2;
    byte unsigned buf_data[$];
    // Collect the data bytes from the packet buffer memory.
    for (int unsigned offset = 0; offset < pkt_len; offset += 4) begin
      logic [31:0] d = read_buffer(buf_start + (offset >> 2));
      buf_data.push_back(d[7:0]);
      if (pkt_len - offset > 1) buf_data.push_back(d[15:8]);
      if (pkt_len - offset > 2) buf_data.push_back(d[23:16]);
      if (pkt_len - offset > 3) buf_data.push_back(d[31:24]);
    end
    data = buf_data;
  endfunction
endclass : usbdev_bfm
