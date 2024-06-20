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
  constraint num_trans_c { num_trans inside {[64:256]}; }

  // Endpoint configuration.
  //
  // Decide upon the Endpoint Type of each endpoint:
  // - Control Endpoints (accept SETUP packets).
  // - Isochronous Endpoints (no handshaking).
  // - Bulk/Interrupt Endpoints; reliable byte stream with
  //   Data Toggle Synchronization and retrying.
  rand bit [NEndpoints-1:0] ep_in_enabled;
  rand bit [NEndpoints-1:0] ep_out_enabled;
  rand bit [NEndpoints-1:0] ep_setup_enabled;
  rand bit [NEndpoints-1:0] ep_iso_enabled;

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

  constraint ep_iso_enabled_c {
    ep_iso_enabled == 0;
  }

  // Bitmap of available buffers that are not presently assigned to the DUT.
  bit [NumBuffers-1:0] buf_avail;

  // We need to track the OUT side Data Toggle(s) otherwise packets will be rejected.
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

  // Number of active streams.
  uint stream_count;

  // Completion indicator for each stream (= pair of endpoints).
  bit [NEndpoints-1:0] stream_completed;

  // Stop the traffic test?
  bit traffic_stop = 0;

  // All traffic transferred successfully?
  bit traffic_completed = 0;

  event device_ready;

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
    usb20_item response;
    `uvm_info(`gfn, $sformatf("Requesting IN packet from EP%d", ep), UVM_HIGH)
    claim_driver();
    // Send IN token packet
    send_token_packet(ep, PidTypeInToken);
    get_response(m_response_item);
    $cast(response, m_response_item);
    case (response.m_pid_type)
      // DATA packet in response.
      PidTypeData0, PidTypeData1: begin
        // Received a packet; check it against expectations.
        data_pkt exp_data;
        data_pkt in_data;
        $cast(in_data, response);
        `DV_CHECK(packets_in_flight[ep].size() > 0)
        exp_data = packets_in_flight[ep].pop_front();
        check_tx_packet(in_data, exp_in_toggle[ep] ? PidTypeData1 : PidTypeData0, exp_data.data);
        if (!ep_iso_enabled[ep]) begin
          // Since we're acknowledging successful receipt, we flip our toggle.
          exp_in_toggle[ep] ^= 1'b1;
          send_handshake(PidTypeAck);
        end
        // Update the count of received packets.
        packets_received[ep] = packets_received[ep] + 1;
        if (packets_received[ep] >= packet_count) stream_completed[ep] = 1'b1;
      end
      // Nothing available, try again later.
      PidTypeNak: begin
      end
      default: `uvm_fatal(`gfn, $sformatf("Unexpected response 0x%0x from DUT",
                          response.m_pid_type))
    endcase
    release_driver();
  endtask

  // Send a pseudo-random packet to the given endpoint number.
  task host_send_out_packet(bit [3:0] ep, bit is_setup);
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
      // Choose the packet length and content pseudo-randomly.
      send_prnd_out_packet(ep, exp_out_toggle[ep] ? PidTypeData1 : PidTypeData0,
                           1'b1, 0, ep_iso_enabled[ep]);
    end
    // Check that the packet was accepted (ACKnowledged) by the USB device.
    // An Isochronous endpoint returns no handshake and no data toggle bit, so do not wait.
    if (ep_iso_enabled[ep]) begin
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
        if (packets_sent[ep_out] < packet_count || ep_iso_enabled[ep_out]) begin
          // Shall we send a SETUP packet rather than an OUT packet?
          bit is_setup = $urandom & ep_setup_enabled[ep_out];
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
    // Update the set of buffers that are available for later use, having not been supplied to
    // the DUT.
    buf_avail[buf_num] = !supplied;
    `uvm_info(`gfn, $sformatf("usbstat was 0x%0x and supplied is %d", usbstat, supplied),
              UVM_HIGH)
  endtask

  // Keep the 'Available Buffer' FIFOs topped up; we want to keep the traffic streaming,
  // so there must always be buffers available to the DUT for packet reception.
  task device_refill_fifos();
    bit supplied = 1'b1;
    // Keep going until we run out of space or buffers.
    while (supplied && buf_avail) begin
      uint buf_num = 0;
      while (buf_num < NumBuffers && !buf_avail[buf_num]) buf_num++;
      `DV_CHECK_FATAL(buf_num < NumBuffers)
      device_buf_supply(buf_num, supplied);
    end
  endtask

  task device_setup;
    // Populate the 'Available Buffer' FIFOs.
    uint buf_num = 0;
    for (uint buf_num = 0; buf_num < NumBuffers; buf_num++) begin
      bit supplied;
      device_buf_supply(buf_num, supplied);
    end
    // Configure the endpoints; this should strictly be done on the device side really.
    csr_wr(.ptr(ral.ep_out_enable[0]),  .value(ep_out_enabled));
    csr_wr(.ptr(ral.ep_in_enable[0]),   .value(ep_in_enabled));
    csr_wr(.ptr(ral.rxenable_out[0]),   .value(ep_out_enabled));
    csr_wr(.ptr(ral.rxenable_setup[0]), .value(ep_setup_enabled));

    ->device_ready;
  endtask

  // Retract the current packet from the given IN endpoint.
  task device_retract_in_packet(bit [3:0] ep, uvm_reg_data_t configin);
    bit supplied;
    // Retraction of IN packet.
    uint prev_buf = get_field_val(ral.configin[0].buffer, configin);
    `uvm_info(`gfn, $sformatf("Retracting IN packet from endpoint %d, buffer %d", ep, prev_buf),
              UVM_MEDIUM)
    ral.configin[ep].rdy.set(1'b0);
    csr_update(ral.configin[ep]);
    // Read back to see whether the packet is being collected right now.
    csr_rd(.ptr(ral.configin[ep]), .value(configin));
    `DV_CHECK_EQ(get_field_val(ral.configin[ep].buffer, configin), prev_buf)
    if (get_field_val(ral.configin[ep].sending, configin)) begin
      // The IN packet is presently being collected; since the packet size is limited to 64 bytes,
      // there is an upper bound on how long the transmission can take. With 4x oversampling, and
      // bit stuffing it's around 'hA30 clock cycles, but difficult to calculate exactly; we just
      // need to ensure that we wait long enough...
      uvm_reg_data_t in_sent;
      for (int unsigned clks = 0; clks < 'hC00; clks++) begin
        csr_rd(.ptr(ral.configin[ep]), .value(configin));
        if (!get_field_val(ral.configin[ep].sending, configin)) break;
      end
      // The packet will have been either accepted or deferred.
      csr_rd(.ptr(ral.in_sent[0]), .value(in_sent));
      `DV_CHECK_FATAL(get_field_val(ral.configin[ep].pend, configin) || in_sent[ep])
      // Clear the 'pending' indicator and the 'sent' status.
      ral.configin[ep].pend.set(1'b1);
      csr_update(ral.configin[ep]);
      csr_wr(.ptr(ral.in_sent[0]), .value(1 << ep));
    end
    device_buf_supply(prev_buf, supplied);
  endtask

  // Present the IN packet for collection.
  task device_present_in_packet(bit [3:0] ep, uint buf_num, uint len);
    uvm_reg_data_t configin;
    `uvm_info(`gfn, $sformatf("EP %d presenting buf %d, %d byte(s)", ep, buf_num, len), UVM_HIGH)
    // Clear the existing IN packet, if there is one (packet retraction).
    csr_rd(.ptr(ral.configin[ep]), .value(configin));
    if (get_field_val(ral.configin[0].rdy, configin)) begin
      device_retract_in_packet(ep, configin);
    end
    // Validate the buffer properties before supplying them to the DUT.
    `DV_CHECK_FATAL(len <= MaxPktSizeByte)
    `DV_CHECK_FATAL(buf_num < NumBuffers)
    ral.configin[ep].size.set(len);
    ral.configin[ep].buffer.set(buf_num);
    ral.configin[ep].rdy.set(1'b0);
    csr_update(ral.configin[ep]);
    // Now set the RDY bit
    ral.configin[ep].rdy.set(1'b1);
    csr_update(ral.configin[ep]);
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
          end
        end
      end

      // Keep the 'Available Buffer' FIFOs topped up.
      device_refill_fifos();

      // Collect and return a received packet if there is one.
      csr_rd(.ptr(ral.usbstat), .value(usbstat));
      if (!get_field_val(ral.usbstat.rx_empty, usbstat)) begin
        uvm_reg_data_t rxfifo;
        csr_rd(.ptr(ral.rxfifo), .value(rxfifo));
        `uvm_info(`gfn, $sformatf("Read RXFIFO 0x%x", rxfifo), UVM_HIGH)

        // Note: in time we may want to modify the packets in some way, but for now we just
        // echo them back and leave the host side to check them.

        // Supply any processed packets for IN collection.
        device_present_in_packet(get_field_val(ral.rxfifo.ep, rxfifo),
                                 get_field_val(ral.rxfifo.buffer, rxfifo),
                                 get_field_val(ral.rxfifo.size, rxfifo));
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
