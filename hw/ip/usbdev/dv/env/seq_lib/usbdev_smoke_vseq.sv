// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class usbdev_smoke_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_smoke_vseq)

  `uvm_object_new

  virtual task body();
    byte unsigned tx_data[];

    // Enable all endpoints for SETUP, IN and OUT
    configure_out_all();
    configure_in_all();
    configure_setup_all();
    csr_wr(.ptr(ral.avsetupbuffer.buffer),
           .value(setup_buffer_id));  // use csr_wr to guarantee write.
    ral.intr_enable.pkt_received.set(1'b1); // Enable pkt_received interrupt
    csr_update(ral.intr_enable);

    // ---------------------------------------------------------------------------------------------
    // SETUP token packet followed by a DATA packet of 8 bytes
    // ---------------------------------------------------------------------------------------------
    send_token_packet(ep_default, PidTypeSetupToken);
    inter_packet_delay();
    call_desc_sequence(PktTypeData, PidTypeData0);
    cfg.clk_rst_vif.wait_clks(20);
    // Check the contents of the packet buffer memory against the SETUP packet that was sent.
    check_rx_packet(ep_default, 1'b1, setup_buffer_id, m_data_pkt.data);

    // ---------------------------------------------------------------------------------------------
    // OUT data packet
    // ---------------------------------------------------------------------------------------------
    csr_wr(.ptr(ral.avoutbuffer.buffer), .value(out_buffer_id));  // use csr_wr to guarantee write.
    // Using DATA1 for second packet, randomized length
    send_prnd_out_packet(ep_default, PidTypeData1, 1, 0);

    // Check that the packet was accepted (ACKnowledged) by the USB device.
    check_response_matches(PidTypeAck);

    // Check the contents of the packet buffer memory against the OUT packet that was sent.
    check_rx_packet(ep_default, 1'b0, out_buffer_id, m_data_pkt.data);

    // ---------------------------------------------------------------------------------------------
    // Retrieve a data packet using an IN transaction.
    // ---------------------------------------------------------------------------------------------
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(tx_data, tx_data.size() <= MaxPktSizeByte;)
    write_buffer(in_buffer_id, tx_data);

    // Declare that there is an IN packet available for collection, initially leaving the RDY bit
    // clear, to mimic the behavior of the DIF.
    ral.configin[ep_default].size.set(tx_data.size());
    ral.configin[ep_default].buffer.set(in_buffer_id);
    ral.configin[ep_default].rdy.set(1'b0);
    csr_update(ral.configin[ep_default]);
    // Now set the RDY bit
    ral.configin[ep_default].rdy.set(1'b1);
    csr_update(ral.configin[ep_default]);

    // Send IN request and collect DATA packet in response.
    send_token_packet(ep_default, PidTypeInToken);
    check_in_packet(PidTypeData1, tx_data);
    // ACKnowledge receipt of the data packet.
    send_handshake(PidTypeAck);
    // in_sent register/interrupt assertion occurs a few cycles after the ACK has been received.
    cfg.clk_rst_vif.wait_clks(20);
    // Verify Transaction reads register status and verifies that IN transaction is successful.
    check_in_sent(ep_default);

  endtask

  // Construct and transmit a DATA packet containing a SETUP descriptor to the USB device
  task call_desc_sequence(input pkt_type_e pkt_type, input pid_type_e pid_type);
    RSP rsp_item;
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    start_item(m_data_pkt);
    m_data_pkt.m_ev_type  = EvPacket;
    m_data_pkt.m_pkt_type = pkt_type;
    m_data_pkt.m_pid_type = pid_type;
    // Construct a GET DESCRIPTOR request that retrieves the Device descriptor
    assert(m_data_pkt.randomize());
    m_data_pkt.make_device_request(bmRequestType3, bRequestGET_DESCRIPTOR,
                                   8'h00, 8'h01,
                                   16'h0, 16'd18);  // Device descriptor >= 18 bytes.
    finish_item(m_data_pkt);
    check_response_matches(PidTypeAck);
  endtask

endclass : usbdev_smoke_vseq
