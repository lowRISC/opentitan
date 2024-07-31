// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Configurable USB streaming test that sends OUT packets to a set of endpoints,
// according to their configuration, and then retrieves those packets from the
// corresponding IN endpoints, checking against the original data.

// Note: In time this may extend from another sequence that introduces bus framing and models
// the behavior/timing of real hosts, rather than just fully utilizing the bus.
//
// The code structure and naming has been written with this in mind, and the intention is that
// some of these tasks would be migrated into the parent 'usbdev_usb_host_vseq.'
class usbdev_max_usb_traffic_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_max_usb_traffic_vseq)

  `uvm_object_new

  // This is the total number of packets to be transferred, across all endpoints.
  constraint num_trans_c { num_trans inside {[32:64]}; }

  // Endpoint configuration.
  //
  // Decide upon the Endpoint Type of each endpoint:
  // - Control Endpoints (accept SETUP packets).
  // - Isochronous Endpoints (no handshaking).
  // - Bulk/Interrupt Endpoints; reliable byte stream with
  //   Data Toggle Synchronization and retrying.
  rand bit [NEndpoints-1:0] ep_in_enabled;
  rand bit [NEndpoints-1:0] ep_out_enabled;
  rand bit [NEndpoints-1:0] rxenable_setup;
  rand bit [NEndpoints-1:0] out_iso;
  rand bit [NEndpoints-1:0] in_iso;

  // Ensure that the test can do something.
  constraint in_and_out_c {
    // OUT data is returned as IN data on the same endpoint.
    (ep_in_enabled & ep_out_enabled) != 0;
  }

  // Ensure that all streams are bidirectional; no OUT endpoints without corresponding IN endpoints
  // and vice-versa.
  constraint bidir_only_c {
    ep_in_enabled == ep_out_enabled;
  }

  // We need to track the OUT side Data Toggle(s) otherwise packets will be dropped.
  bit [NEndpoints-1:0] exp_out_toggle;

  // We track the IN side Data Toggle(s) just to check that the DUT transmissions.
  bit [NEndpoints-1:0] exp_in_toggle;

  // Number of packets to be transferred per stream.
  uint packet_count;

  // Number of packets sent to each OUT endpoint.
  uint packets_sent[NEndpoints];
  // Number of packets received from each IN endpoint.
  uint packets_received[NEndpoints];

  // In-flight packets to each of the endpoints.
  data_pkt packets_in_flight[NEndpoints][$];

  // Description of a packet received on the device side.
  typedef struct {
    byte unsigned data[];
  } rx_packet_t;

  // Device-side queue of packets
  // - Non-Isochronous streams are not permitted to drop packets.
  // - A stream is considered non-Isochronous if neither OUT nor IN endpoint is Isochronous.
  rx_packet_t dev_pkt_q[NEndpoints][$];

  // Number of active streams.
  uint stream_count;

  // Completion indicator for each stream (= pair of endpoints).
  bit [NEndpoints-1:0] stream_completed;

  // Stop the traffic test?
  bit traffic_stop = 0;

  // All traffic transferred successfully?
  bit traffic_completed = 0;

  event device_ready;

  // Extract the sequence ID from the start of a DATA packet.
  function bit [31:0] get_sequence_id(ref byte unsigned data[]);
    bit [31:0] seq_id;
    // Packet data shall always consist of at least four bytes.
    `DV_CHECK_GE(data.size(), 4)
    seq_id = {data[3], data[2], data[1], data[0]};
    `uvm_info(`gfn, $sformatf("get_sequence_id returning 0x%0x", seq_id), UVM_HIGH)
    return seq_id;
  endfunction

  // ------------------------------------ Host side of test --------------------------------------

  // Set up the host-side state.
  task host_setup();
    // Ensure all packet buffer expectations are defined but empty.
    for (int unsigned ep = 0; ep < NEndpoints; ep++) begin
      packets_in_flight[ep].delete();
      packets_received[ep] = 0;
    end
    // TODO: we should ideally detect this over the USB itself with changes to the usb20_driver
    //       to test the state of the pull ups.
    wait (device_ready.triggered);
  endtask

  // Attempt to collect an IN packet from the given endpoint.
  task host_collect_in_packet(bit [3:0] ep);
    bit iso = in_iso[ep];
    usb20_item response;
    RSP rsp;
    `uvm_info(`gfn, $sformatf("Requesting IN packet from EP%d", ep), UVM_HIGH)
    claim_driver();
    // Send IN token packet
    send_token_packet(ep, PidTypeInToken);
    get_response(rsp);
    $cast(response, rsp);
    case (response.m_pid_type)
      // DATA packet in response.
      PidTypeData0, PidTypeData1: begin
        pid_type_e exp_pid = (exp_in_toggle[ep] & !iso) ? PidTypeData1 : PidTypeData0;
        // Received a packet; check it against expectations.
        data_pkt exp_data;
        data_pkt in_data;
        $cast(in_data, response);
        // Ignore Zero Length Packets from Isochronous endpoints because this just means there is no
        // data available presently. (This sequence does not generate zero length packets.)
        if (!iso || in_data.data.size() > 0) begin
          bit [31:0] act_seq = get_sequence_id(in_data.data);
          bit [31:0] exp_seq;
          do begin
            `DV_CHECK(packets_in_flight[ep].size() > 0)
            exp_data = packets_in_flight[ep].pop_front();
            // Isochronous streams may drop OUT and/or IN packets, so use the sequence number to
            // catch up.
            exp_seq = get_sequence_id(exp_data.data);
            `uvm_info(`gfn, $sformatf("Comparing act seq 0x%0x against exp 0x%0x (iso %0d)",
                                      act_seq, exp_seq, iso), UVM_MEDIUM)
          end while (iso && exp_seq < act_seq);
          // This packet should match; content check includes the sequence IDs.
          check_tx_packet(in_data, exp_pid, exp_data.data);
          if (!iso) begin
            // Since we're acknowledging successful receipt, we flip our toggle.
            exp_in_toggle[ep] ^= 1'b1;
            send_handshake(PidTypeAck);
          end
          // Update the count of received packets.
          packets_received[ep] = packets_received[ep] + 1;
          if (packets_received[ep] >= packet_count) stream_completed[ep] = 1'b1;
        end
      end
      // Nothing available, try again later.
      PidTypeNak: begin
        `DV_CHECK_EQ(iso, 1'b0, "Only non-Isochronous endpoints should NAK IN requests")
      end
      default: `uvm_fatal(`gfn, $sformatf("Unexpected response 0x%0x from DUT",
                          response.m_pid_type))
    endcase
    release_driver();
  endtask

  // Send a pseudo-random packet to the given endpoint number.
  task host_send_out_packet(bit [3:0] ep, bit is_setup);
    bit iso = out_iso[ep];
    `uvm_info(`gfn, $sformatf("Sending OUT packet to EP%d", ep), UVM_HIGH)
    claim_driver();
    if (is_setup) begin
      send_prnd_setup_packet(ep);
      // Sending a SETUP packet clears the data toggle on the OUT side and it will then toggle
      // upon successful receipt of the OUT packet.
      exp_out_toggle[ep] = 1'b0;
      // The IN side is advanced automatically.
      exp_in_toggle[ep]  = 1'b1;
    end else begin
      // Choose the packet length and content pseudo-randomly, but ensure that we have at least
      // 4 bytes so that we can include a packet sequence number to differentiate the packets.
      // As an extra precaution we set the 4 MSBs to match the endpoint number, which can also be
      // diagnostically useful.
      uint seq_id = packets_sent[ep];
      byte unsigned data[];
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data, data.size() >= 4 && data.size() <= MaxPktSizeByte;)
      {data[3], data[2], data[1], data[0]} = {ep, seq_id[27:0]};
      send_out_packet(ep, exp_out_toggle[ep] ? PidTypeData1 : PidTypeData0, data, iso);
    end
    // Check that the packet was accepted (ACKnowledged) by the USB device.
    // An Isochronous endpoint returns no handshake and no data toggle bit, so do not wait.
    if (iso) begin
      // Ensure a sufficient gap before the next transaction.
      // TODO: this should probably be guaranteed within the driver.
      inter_packet_delay();
    end else begin
      check_response_matches(PidTypeAck);
      // Packet successfully received and ACKnowledged; flip the data toggle.
      exp_out_toggle[ep] ^= 1'b1;
    end
    release_driver();
    // Remember the packet for subsequent checking.
    packets_in_flight[ep].push_back(m_data_pkt);
    // Update the count of transmitted packets.
    packets_sent[ep] = packets_sent[ep] + 1;
  endtask

  // Update state to reflect the fact that a Bus Reset has been sent to the DUT.
  virtual task host_side_handle_bus_reset();
    // Bus Reset clears all data toggle bits within the DUT.
    exp_out_toggle = {NEndpoints{1'b0}};
    exp_in_toggle = {NEndpoints{1'b0}};
  endtask

  // Host controller.
  task host_side;
    // Round-robin servicing of IN and OUT endpoints.
    uint ep_out = 0;
    uint ep_in = 0;

    host_setup();
    do begin
      // Remember the current endpoints numbers.
      uint prev_out = ep_out;
      uint prev_in = ep_in;

      // Attempt to collect an IN packet.
      do begin
        ep_in++;
        if (ep_in >= NEndpoints) ep_in = 0;
      end while (ep_in != prev_in && (!ep_in_enabled[ep_in] || stream_completed[ep_in]));
      if (ep_in_enabled[ep_in] && !stream_completed[ep_in]) begin
        host_collect_in_packet(ep_in);
      end

      // Attempt to transmit a SETUP/OUT packet.
      do begin
        ep_out++;
        if (ep_out >= NEndpoints) ep_out = 0;
      end while (ep_out != prev_out && (!ep_out_enabled[ep_out] || stream_completed[ep_out]));
      if (ep_out_enabled[ep_out] && !stream_completed[ep_out]) begin
        // Are we permitted to send another OUT packet?
        // - Isochronous streams continue transmitting until we have received the required
        //   number of IN packets, since packets may be lost in either direction.
        if (packets_sent[ep_out] < packet_count || out_iso[ep_out]) begin
          // Shall we send a SETUP packet rather than an OUT packet?
          bit is_setup = $urandom & rxenable_setup[ep_out];
          host_send_out_packet(ep_out, is_setup);
        end
      end

      traffic_completed = &{stream_completed | ~ep_in_enabled | ~ep_out_enabled};
    end while (!traffic_completed);

    // Stop all other processes, we've finished.
    traffic_stop = 1;
  endtask

  // ----------------------------------- Device side of test -------------------------------------

  // Attempt to supply the specified packet buffer to the DUT for reception.
  task device_buf_supply(uint buf_num, output bit supplied);
    uvm_reg_data_t usbstat;
    `uvm_info(`gfn, $sformatf("Supplying buffer %d for use", buf_num), UVM_HIGH)
    // Fill the SETUP Buffer FIFO first; this is smaller and more important than the
    // FIFO for regular OUT buffers.
    csr_rd(.ptr(ral.usbstat), .value(usbstat));
    `uvm_info(`gfn, $sformatf(" - usbstat 0x%x", usbstat), UVM_HIGH)
    if (get_field_val(ral.usbstat.av_setup_full, usbstat)) begin
      if (get_field_val(ral.usbstat.av_out_full, usbstat)) begin
        supplied = 1'b0;
      end else begin
        csr_wr(.ptr(ral.avoutbuffer), .value(buf_num));
        supplied = 1'b1;
      end
    end else begin
      csr_wr(.ptr(ral.avsetupbuffer), .value(buf_num));
      supplied = 1'b1;
    end
    `uvm_info(`gfn, $sformatf("usbstat was 0x%0x and supplied is %d", usbstat, supplied),
              UVM_HIGH)
  endtask

  // Keep the 'Available Buffer' FIFOs topped up; we want to keep the traffic streaming,
  // so there must always be buffers available to the DUT for packet reception.
  task device_refill_fifos();
    int buf_num = buf_alloc();
    bit supplied = 1'b1;
    // Keep going until we run out of space or buffers.
    while (supplied && buf_num >= 0) begin
      device_buf_supply(buf_num, supplied);
      if (supplied) buf_num = buf_alloc();
    end
    if (buf_num >= 0) buf_release(buf_num);
  endtask

  task device_setup;
    buf_init();
    // Populate the 'Available Buffer' FIFOs.
    device_refill_fifos();
    // Configure the endpoints; this should strictly be done on the device side really.
    csr_wr(.ptr(ral.ep_out_enable[0]),  .value(ep_out_enabled));
    csr_wr(.ptr(ral.ep_in_enable[0]),   .value(ep_in_enabled));
    csr_wr(.ptr(ral.rxenable_out[0]),   .value(ep_out_enabled));
    csr_wr(.ptr(ral.rxenable_setup[0]), .value(rxenable_setup));
    csr_wr(.ptr(ral.out_iso[0]),        .value(out_iso));
    csr_wr(.ptr(ral.in_iso[0]),         .value(in_iso));

    // Report the configuration that we're using.
    `uvm_info(`gfn, $sformatf("ep_out_enable  0x%0x", ep_out_enabled), UVM_LOW)
    `uvm_info(`gfn, $sformatf("ep_in_enable   0x%0x", ep_in_enabled),  UVM_LOW)
    `uvm_info(`gfn, $sformatf("rxenable_out   0x%0x", ep_out_enabled), UVM_LOW)
    `uvm_info(`gfn, $sformatf("rxenable_setup 0x%0x", rxenable_setup), UVM_LOW)
    `uvm_info(`gfn, $sformatf("out_iso        0x%0x", out_iso),        UVM_LOW)
    `uvm_info(`gfn, $sformatf("in_iso         0x%0x", in_iso),         UVM_LOW)

    // Control endpoint setting takes precedence over the Isochronous one; having both bits set
    // for a single endpoint constitutes a configuration error, but we want to exercise all
    // configurations.
    out_iso &= ~rxenable_setup;
    in_iso  &= ~rxenable_setup;

    // Ensure that our packet queues are defined and empty.
    for (int unsigned ep = 0; ep < NEndpoints; ep++) dev_pkt_q[ep].delete();

    ->device_ready;
  endtask

  // Device side response to a Bus Reset being issued.
  virtual task device_side_handle_bus_reset();
    // We must reinstate the device address following a bus reset.
    csr_wr(.ptr(ral.usbctrl.device_address), .value(dev_addr));
    // Endpoint configuration is retained within the DUT but any IN-side packets should have had
    // their 'RDY' bit cleared.
    // Since the host-side code does not know whether an OUT packet has been presented for
    // collection or is still sitting in the RX FIFO, for simplicity we just re-present pending IN
    // packets.
    for (int unsigned ep = 0; ep < NEndpoints; ep++) begin
      uvm_reg_data_t configin;
      csr_rd(.ptr(ral.configin[ep]), .value(configin));
      if (get_field_val(ral.configin[ep].pend, configin)) begin
        // Clear both the 'pend' and 'rdy' bits.
        ral.configin[ep].pend.set(1'b1);
        ral.configin[ep].rdy.set(1'b0);
        csr_update(ral.configin[ep]);
        // Present the packet again by setting the 'rdy' bit.
        ral.configin[ep].rdy.set(1'b1);
        csr_update(ral.configin[ep]);
      end
    end
  endtask

  // Device side, CSR access; this simple task just returns all received
  // packets unmodified to the host for it to check.
  task device_side;
    device_setup();

    while (!traffic_stop) begin
      uvm_reg_data_t in_sent;
      uvm_reg_data_t usbstat;

      // Return any buffers that are now available.
      csr_rd(.ptr(ral.in_sent[0]), .value(in_sent));
      if (in_sent) begin
        csr_wr(.ptr(ral.in_sent[0]), .value(in_sent));
        `uvm_info(`gfn, $sformatf("Read in_sent 0x%x", in_sent), UVM_HIGH)
        for (uint ep = 0; ep < NEndpoints; ep++) begin
          if (in_sent[ep]) begin
            uvm_reg_data_t configin;
            uint buf_num;
            bit supplied;
            csr_rd(.ptr(ral.configin[ep]), .value(configin));
            `DV_CHECK_EQ(get_field_val(ral.configin[0].rdy, configin), 1'b0, "RDY bit is still set")
            // Return this buffer.
            buf_num = get_field_val(ral.configin[0].buffer, configin);
            device_buf_supply(buf_num, supplied);
            if (!supplied) buf_release(buf_num);
          end
        end
      end

      // Keep the 'Available Buffer' FIFOs topped up.
      device_refill_fifos();

      // Collect and return a received packet if there is one.
      csr_rd(.ptr(ral.usbstat), .value(usbstat));
      if (!get_field_val(ral.usbstat.rx_empty, usbstat)) begin
        uvm_reg_data_t rxfifo;
        int unsigned buf_num;
        int unsigned pkt_len;
        bit enqueue = 1'b1;
        bit [3:0] ep;

        csr_rd(.ptr(ral.rxfifo), .value(rxfifo));
        `uvm_info(`gfn, $sformatf("Read RXFIFO 0x%x", rxfifo), UVM_HIGH)

        ep = get_field_val(ral.rxfifo.ep, rxfifo);
        buf_num = get_field_val(ral.rxfifo.buffer, rxfifo);
        pkt_len = get_field_val(ral.rxfifo.size, rxfifo);
        `uvm_info(`gfn, $sformatf("Device ep %0d received %0d byte(s) into buffer %0d", ep,
                                  pkt_len, buf_num), UVM_MEDIUM)
        `DV_CHECK_LT(ep, NEndpoints)

        // Note: in time we may want to modify the packets in some way, but for now we just
        // echo them back and leave the host side to check them.

        // If we already have packets queued for this endpoint, we must queue this packet too, to
        // keep them in order.
        if (!dev_pkt_q[ep].size()) begin
          bit iso = in_iso[ep];
          uvm_reg_data_t rdy;
          // Is there still a waiting IN packet for this endpoint?
          csr_rd(.ptr(ral.configin[ep].rdy), .value(rdy));
          if (iso || !rdy) begin
            int unsigned retracted_buf;
            bit retracted;
            // We should be able to make the packet available immediately, leaving it in its present
            // buffer. Present the packet for collection by an IN transaction from the USB host.
            present_in_packet(ep, buf_num, pkt_len, .may_retract(iso), .retracted(retracted),
                              .retracted_buf(retracted_buf));
            // Was a packet retracted?
            if (retracted) begin
              bit supplied;
              device_buf_supply(retracted_buf, supplied);
            end
            enqueue = 1'b0;
          end
        end
        if (enqueue) begin
          // Collect the contents of the packet buffer.
          rx_packet_t rx_pkt;
          bit supplied;
          read_buffer(buf_num, pkt_len, rx_pkt.data);
          dev_pkt_q[ep].push_back(rx_pkt);
          // Release the buffer.
          device_buf_supply(buf_num, supplied);
          if (!supplied) buf_release(buf_num);
        end
      end

      // Can we supply any more packets for IN collection at this point?
      // Do as many as we can right now, just to keep things moving.
      for (int unsigned ep = 0; ep < NEndpoints; ep++) begin
        if (ep_in_enabled[ep] && dev_pkt_q[ep].size() > 0) begin
          uvm_reg_data_t rdy;
          csr_rd(.ptr(ral.configin[ep].rdy), .value(rdy));
          if (!rdy) begin
            int buf_num = buf_alloc();
            if (buf_num >= 0) begin
              rx_packet_t rx_pkt = dev_pkt_q[ep].pop_front();
              int unsigned pkt_len = rx_pkt.data.size();
              int unsigned retracted_buf;
              bit iso = in_iso[ep];
              bit retracted;
              write_buffer(buf_num, rx_pkt.data);
              present_in_packet(ep, buf_num, pkt_len, .may_retract(iso),
                                .retracted(retracted), .retracted_buf(retracted_buf));
              `DV_CHECK_EQ(retracted, 0, "Should not have had to retract an IN packet here")
            end
          end
        end
      end
    end
  endtask

  // Perform Suspend-Resume Signaling.
  virtual task suspend_resume(int unsigned duration_usecs = 0);
    claim_driver();
    // Suspend Signaling.
    super.send_suspend_signaling(); // Default duration.
    // Resume Signaling.
    super.send_resume_signaling(duration_usecs);
    release_driver();
  endtask

  // Issue a Bus Reset to the DUT.
  virtual task send_bus_reset(int unsigned duration_usecs = 0);
    claim_driver();
    super.send_bus_reset(duration_usecs);
    // Both the USB host-side and the device-side code must be informed of bus resets, in order
    // to update their states appropriately.
    host_side_handle_bus_reset();
    device_side_handle_bus_reset();
    release_driver();
  endtask

  // Disconnect VBUS for the specified number of microseconds.
  virtual task vbus_disconnect(int unsigned disconn_duration_usecs,
                               int unsigned reset_duration_usecs = 0);
    claim_driver();
    set_vbus_state(1'b0);
    // VBUS interruption
    cfg.clk_rst_vif.wait_clks(disconn_duration_usecs * 48);
    set_vbus_state(1'b1);
    // On physical buses with real hosts there would be a much longer delay here to allow power
    // supplies to stabilize and the device become ready to respond to the Bus Reset.
    cfg.clk_rst_vif.wait_clks(128);
    // Following VBUS connection we must perform a Bus Reset on the DUT.
    super.send_bus_reset(reset_duration_usecs);
    // Both the USB host-side and the device-side code must be informed of bus resets, in order
    // to update their states appropriately.
    host_side_handle_bus_reset();
    device_side_handle_bus_reset();
    release_driver();
  endtask

  virtual task body;
    // Determine the number of streams and the packets/stream.
    stream_count = $countones(ep_in_enabled & ep_out_enabled);
    `DV_CHECK_NE(stream_count, 0)
    packet_count = num_trans / stream_count;
    `uvm_info(`gfn, $sformatf("Transferring %d packets for each of %d stream(s)", packet_count,
                              stream_count), UVM_LOW)
    // The test runs until all packets have been successfully received and checked by the host.
    fork
      host_side();
      device_side();
    join
  endtask

endclass : usbdev_max_usb_traffic_vseq
