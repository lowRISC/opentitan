// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// USBDEV packet buffer test sequence
//
// Employing randomization, sufficient transactions and coverage:
//
// - read and write the entire packet buffer memory from the CSR side
// - read and write from/to every buffer on the USB side
// - produce temporal collisions between the CSR side and the USB side;
//   - The DUT does not need to handle simultaneous access to the same packet
//     buffer from both sides because the software is responsible for ensuring
//     that this does not happen.
//   - It does, however, need to handle simultaneous accesses to the packet
//     buffer memory because all of the buffers are stored within a single
//     RAM.

class usbdev_pkt_buffer_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_pkt_buffer_vseq)

  `uvm_object_new

  // Large number of transactions to try to cover all packet buffers and increase the chance of
  // simultaneous packet buffer accesses from CSR and USB sides.
  constraint num_trans_c { num_trans inside {[256:1024]}; }

  // Endpoint number being tested.
  bit [3:0] ep;

  // Amount of valid/defined data in each of the packet buffers; zero initialized and the
  // values increase as the sequence advances.
  int unsigned valid_len[NumBuffers];

  // Expected contents of each packet buffer.
  byte unsigned exp_data[NumBuffers][$];

  // We need to track the OUT side Data Toggle(s) otherwise packets will be rejected;
  bit exp_out_toggle[NEndpoints];
  // Similarly for the IN side; these both default to zeros.
  bit exp_in_toggle[NEndpoints];

  // OUT component (host -> device) of the USB side of the test.
  task usb_side_out(int unsigned usb_buf);
    // Expected data content of packet
    byte unsigned pkt_data[];
    int unsigned usb_len;
    usb20_item response;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(usb_len, usb_len inside {[0:MaxPktSizeByte]};)
    `uvm_info(`gfn, $sformatf("USB sending an OUT packet of 0x%x byte(s) to buffer 0x%x",
                              usb_len, usb_buf), UVM_MEDIUM)
    // Supply the buffer
    csr_wr(.ptr(ral.avoutbuffer), .value(usb_buf));

    // If we have just completed an IN transaction with a handshake response we must ensure at
    // least 2 bit intervals of Idle before the OUT transaction here.
    //
    // TODO: this should probably be checked and enforced in the usb20_driver rather than in the
    //       vseqs where it will be susceptible to oversight.
    inter_packet_delay();

    send_prnd_out_packet(ep, exp_out_toggle[ep] ? PidTypeData1 : PidTypeData0, 0, usb_len);
    // Check that the packet was accepted (ACKnowledged) by the USB device.
    check_response_matches(PidTypeAck);

    // Given that the packet has been accepted, we must flip the OUT Data Toggle.
    exp_out_toggle[ep] ^= 1;

    // Check the contents of the packet buffer memory against the OUT packet that was sent.
    check_rx_packet(ep, 1'b0, usb_buf, m_data_pkt.data);

    // This is now the expected content of the packet buffer
    valid_len[usb_buf] = pkt_data.size();
    exp_data[usb_buf]  = pkt_data;
  endtask

  // IN component (device -> host) of the USB side of the test.
  task usb_side_in(int unsigned usb_buf);
    byte unsigned pkt_data[];
    int unsigned usb_len;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(usb_len, usb_len inside {[0:valid_len[usb_buf]]};)
    `uvm_info(`gfn, $sformatf("USB retrieving an IN packet of 0x%x byte(s) from buffer 0x%x",
                              usb_len, usb_buf), UVM_MEDIUM)

    // Pick up the portion of the packet that we intended to retrieve from the USB device.
    if (usb_len > 0) pkt_data = exp_data[usb_buf][0:usb_len-1];

    // Present the IN packet for collection.
    ral.configin[ep].size.set(usb_len);
    ral.configin[ep].buffer.set(usb_buf);
    ral.configin[ep].rdy.set(1'b0);
    csr_update(ral.configin[ep]);
    // Now set the RDY bit
    ral.configin[ep].rdy.set(1'b1);
    csr_update(ral.configin[ep]);

    // Token pkt followed by handshake pkt
    send_token_packet(ep, PidTypeInToken);
    check_in_packet(exp_in_toggle[ep] ? PidTypeData1 : PidTypeData0, pkt_data);
    send_handshake(PidTypeAck);

    // Flip the IN side Data Toggle in anticipation of the next packet transfer.
    exp_in_toggle[ep] ^= 1;
  endtask

  // USB side of test.
  task usb_side(int unsigned usb_buf);
    // Decide on the direction of USB traffic.
    bit usb_wr;
    `DV_CHECK_STD_RANDOMIZE_FATAL(usb_wr)

    // Choose a new endpoint
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(ep, ep inside {[0:NEndpoints-1]};)

    // Initiate writing of the buffer
    if (usb_wr) begin
      usb_side_out(usb_buf);
    end else begin
      usb_side_in(usb_buf);
    end
  endtask

  // CSR side of test.
  task csr_side(int unsigned csr_buf);
    // Decide on the direction of CSR traffic.
    bit csr_wr;
    `DV_CHECK_STD_RANDOMIZE_FATAL(csr_wr)
    if (csr_wr) begin
      // Generate some random data, write it to the packet buffer and update our expectation.
      byte unsigned pkt[];
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(pkt, pkt.size() inside {[0:MaxPktSizeByte]};)
      valid_len[csr_buf] = pkt.size();
      exp_data[csr_buf] = pkt;
      `uvm_info(`gfn, $sformatf("CSR side writing 0x%x byte(s) to buffer 0x%x",
                                pkt.size(), csr_buf), UVM_MEDIUM)
      write_buffer(csr_buf, exp_data[csr_buf]);
    end else begin
      `uvm_info(`gfn, $sformatf("CSR checking 0x%x byte(s) in buffer 0x%x",
                                valid_len[csr_buf], csr_buf), UVM_MEDIUM)
      // Read and check the contents of this packet buffer against the captured expectations.
      read_check_buffer(csr_buf, exp_data[csr_buf]);
    end
  endtask

  task body;
    // Enable all endpoints for both IN and OUT traffic.
    configure_out_all();
    configure_in_all();

    // Ensure all packet buffer expectations are defined but empty.
    for (int unsigned b = 0; b < NumBuffers; b++) begin
      exp_data[b].delete();
    end

    // Do not proceed further until the device has exited the Bus Reset signaling of the
    // usb20_driver module.
    wait_for_link_state({LinkActive, LinkActiveNoSOF}, 10 * 1000 * 48);  // 10ms timeout, at 48MHz

    for (int unsigned txn = 0; txn < num_trans; txn++) begin
      int unsigned csr_buf;
      int unsigned usb_buf;
      // Choose a random buffer and direction for the CSR side access.
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(csr_buf, csr_buf inside {[0:NumBuffers-1]};)
      // Choose a random packet buffer and direction for the USB side, ensuring that it does not
      // access the same buffer as the CSR side.
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(usb_buf,
                                         usb_buf inside {[0:NumBuffers-1]}; usb_buf != csr_buf;)
      fork
        csr_side(csr_buf);
        usb_side(usb_buf);
      join
    end
  endtask

endclass
