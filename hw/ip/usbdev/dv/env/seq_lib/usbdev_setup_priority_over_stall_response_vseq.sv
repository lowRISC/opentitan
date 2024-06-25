// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_setup_priority_over_stall_response_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_setup_priority_over_stall_response_vseq)

  `uvm_object_new

  // Check the STALL state is as expected for the given endpoint.
  task check_stall_state(bit [3:0] ep, bit exp_out_stall, bit exp_in_stall);
    uvm_reg_data_t act_out_stall;
    uvm_reg_data_t act_in_stall;
    csr_rd(.ptr(ral.out_stall[0]), .value(act_out_stall));
    `DV_CHECK_EQ(act_out_stall[ep], exp_out_stall, "OUT STALL bit not as expected")
    csr_rd(.ptr(ral.in_stall[0]), .value(act_in_stall));
    `DV_CHECK_EQ(act_in_stall[ep], exp_in_stall, "IN STALL bit not as expected")
  endtask

  virtual task body();
    // Properties of OUT transaction.
    int unsigned num_of_bytes = 0;
    bit randomize_length = 1'b1;
    // Stimulus after OUT transaction.
    bit bus_reset = 1'b0;

    // Related to closed issue #23806 we need to be sure that we generate long packets that yield a
    // STALL response, and ideally long packets for which we then issue a bus reset before the
    // ACK/NAK.
    //
    // Note: unfortunately with the present driver structure we cannot generate a link reset
    // part-way through transmitting an OUT packet to the device, and ideally we need to hit the
    // point at which 62-64 bytes have been transmitted but there has been no ACK/NAK response.
    randcase
      1: begin
        // Nothing to do...default configuration suffices.
      end
      1: begin
        randomize_length = 1'b0;
        num_of_bytes = 62;
      end
      // Don't STALL the OUT packet, but DO ensure that it's a long packet and _then_ issue a
      // Bus Reset.
      1: begin
        randomize_length = 1'b0;
        bus_reset = 1'b1;
        num_of_bytes = 63;
      end
    endcase
    // Report chosen stimulus.
    `uvm_info(`gfn, $sformatf("Decided to send OUT transaction of %0d byte(s), bus reset %0d",
                              num_of_bytes, bus_reset), UVM_MEDIUM)

    // Enable the endpoint for all transaction types.
    configure_out_trans(ep_default);
    configure_in_trans(ep_default, in_buffer_id, .num_of_bytes(0));
    // Note: this also supplies a buffer to the SETUP DATA packet.
    configure_setup_trans(ep_default);

    // Configure an endpoint to generate a STALL handshake in response to IN or OUT transactions.
    configure_out_stall(ep_default);
    configure_in_stall(ep_default);

    check_stall_state(ep_default, .exp_out_stall(1'b1), .exp_in_stall(1'b1));

    // Check that an OUT transaction is not accepted now that we have enabled STALLing.
    send_prnd_out_packet(ep_default, PidTypeData0, randomize_length, num_of_bytes);
    check_response_matches(PidTypeStall);
    // Issue a Bus Reset at this point? See the note above; ideally we'd send the bus reset
    // overlapped with the OUT transaction.
    if (bus_reset) begin
      send_bus_reset(100);
      // Following a Bus Reset we need to reinstate the device address.
      usbdev_set_address(dev_addr);
    end else begin
      // Check that an IN transaction is not accepted either.
      usb20_item item;
      retrieve_in_packet(ep_default, item, .ack(0));
      item.check_pid_type(PidTypeStall);
    end

    // Attempt to send a SETUP transaction to this endpoint.
    send_prnd_setup_packet(ep_default);
    // We should get no STALL at this point; the receipt of SETUP transactions is more important,
    // so it should be ACKnowledged.
    check_response_matches(PidTypeAck);

    check_stall_state(ep_default, .exp_out_stall(1'b0), .exp_in_stall(1'b0));
    // We may as well check the received packet too; this also empties the RX FIFO.
    check_rx_packet(ep_default, .setup(1), .exp_buffer_id(setup_buffer_id),
                    .exp_byte_data(m_data_pkt.data), .buffer_known(1));
  endtask
endclass : usbdev_setup_priority_over_stall_response_vseq
