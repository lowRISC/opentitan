// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class usbdev_smoke_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_smoke_vseq)

  `uvm_object_new

  task body();
    // Expected data content of packet
    byte unsigned exp_data[];
    usb20_item response;
    data_pkt in_data;

    super.apply_reset("HARD");
    super.dut_init("HARD");
    cfg.clk_rst_vif.wait_clks(200);
    clear_all_interrupts();

    // Enable all endpoints for SETUP, IN and OUT
    csr_wr(.ptr(ral.ep_out_enable[0]), .value(12'hfff));
    csr_wr(.ptr(ral.ep_in_enable[0]), .value(12'hfff));
    csr_wr(.ptr(ral.rxenable_out[0]), .value(12'hfff));
    csr_wr(.ptr(ral.rxenable_setup[0]), .value(12'hfff));
    ral.avsetupbuffer.buffer.set(setup_buffer_id); // set buffer id =1
    csr_update(ral.avsetupbuffer);
    ral.intr_enable.pkt_received.set(1'b1); // Enable pkt_received interrupt
    csr_update(ral.intr_enable);

    // ---------------------------------------------------------------------------------------------
    // SETUP token packet followed by a DATA packet of 8 bytes
    // ---------------------------------------------------------------------------------------------
    call_token_seq(PidTypeSetupToken);
    cfg.clk_rst_vif.wait_clks(20);
    call_desc_sequence(PktTypeData, PidTypeData0);
    cfg.clk_rst_vif.wait_clks(20);

    // Check the contents of the packet buffer memory against the SETUP packet that was sent.
    recover_orig_data(m_data_pkt.data, exp_data);
    check_rx_packet(endp, 1'b1, setup_buffer_id, exp_data);

    // ---------------------------------------------------------------------------------------------
    // OUT data packet
    // ---------------------------------------------------------------------------------------------
    ral.avoutbuffer.buffer.set(out_buffer_id);
    csr_update(ral.avoutbuffer);
    call_token_seq(PidTypeOutToken);
    cfg.clk_rst_vif.wait_clks(20);
    // TODO: want to use a randomized packet length here but may be 4n contrained presently.
    call_data_seq(PidTypeData1, 0, 64);  // Using DATA1 for second packet.
    cfg.clk_rst_vif.wait_clks(20);

    // Check that the packet was accepted (ACKnowledged) by the USB device.
    get_response(m_response_item);
    $cast(response, m_response_item);
    `DV_CHECK_EQ(response.m_pkt_type, PktTypeHandshake);
    `DV_CHECK_EQ(response.m_pid_type, PidTypeAck);

    // Check the contents of the packet buffer memory against the OUT packet that was sent.
    recover_orig_data(m_data_pkt.data, exp_data);
    check_rx_packet(endp, 1'b0, out_buffer_id, exp_data);

    // ---------------------------------------------------------------------------------------------
    // Retrieve that data packet using an IN transaction.
    // ---------------------------------------------------------------------------------------------

    // Declare that there is an IN packet available for collection, initially leaving the RDY bit
    // clear, to mimic the behavior of the DIF.
    ral.configin[endp].size.set(exp_data.size());
    ral.configin[endp].buffer.set(out_buffer_id);
    ral.configin[endp].rdy.set(1'b0);
    csr_update(ral.configin[endp]);
    // Now set the RDY bit
    ral.configin[endp].rdy.set(1'b1);
    csr_update(ral.configin[endp]);

    // Token pkt followed by handshake pkt
    call_token_seq(PidTypeInToken);
    get_response(m_response_item);
    $cast(response, m_response_item);
    `DV_CHECK_EQ(response.m_pkt_type, PktTypeData);
    $cast(in_data, response);
    check_tx_packet(in_data, PidTypeData1, exp_data);
    cfg.clk_rst_vif.wait_clks(20);
    call_handshake_sequence(PktTypeHandshake, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    // Verify Transaction reads register status and verifies that IN transaction is successful.
    check_in_sent();

  endtask

  // TODO: Presently the act of sending a data packet, destructively modifies it!
  // Restore the data packet to its original state. This just bit-reverses each byte
  // within the input array.
  function recover_orig_data(input byte unsigned in[], output byte unsigned out[]);
    out = {<<8{in}};  // Reverse the order of the bytes
    out = {<<{out}};  // Bit-reverse everything
  endfunction

  // Construct and transmit a DATA packet containing a SETUP descriptor to the USB device
  task call_desc_sequence(input pkt_type_e pkt_type, input pid_type_e pid_type);
    usb20_item response;
    RSP rsp_item;
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    m_data_pkt.m_pkt_type = pkt_type;
    m_data_pkt.m_pid_type = pid_type;
    m_data_pkt.m_bmRT = bmRequestType3;
    m_data_pkt.m_bR = bRequestGET_DESCRIPTOR;
    assert(m_data_pkt.randomize());
    m_data_pkt.set_payload(m_data_pkt.m_bmRT, m_data_pkt.m_bR, 8'h00, 8'h01, 8'h00, 8'h00,
                           8'h40,8'h00);
    start_item(m_data_pkt);
    finish_item(m_data_pkt);
    get_response(rsp_item);
    $cast(response, rsp_item);
    get_out_response_from_device(response, PidTypeAck);
  endtask

endclass : usbdev_smoke_vseq
