// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_device_address_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_device_address_vseq)

  `uvm_object_new

  virtual task body();
    bit      [6:0] set_dev_addr;
    uvm_reg_data_t data;

    // SETUP TRANS to default USB device address 0.
    // -------------------------------
    configure_setup_trans();
    csr_wr(.ptr(ral.rxenable_setup[0].setup[0]), .value(1'b1));
    csr_wr(.ptr(ral.ep_out_enable[0].enable[0]), .value(1'b1));

    // Send setup token packet followed by a data packet.
    call_token_seq_to_set_addr(PidTypeSetupToken, .dev_addr(7'h0));
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b0), .num_of_bytes(8));

    // Check that the packet was accepted (ACKnowledged) by the USB device.
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    `DV_CHECK_EQ(m_usb20_item.m_pkt_type, PktTypeHandshake);
    `DV_CHECK_EQ(m_usb20_item.m_pid_type, PidTypeAck);

    // Read memory to extract address.
    for(int i = 0 ;i < 1; i++) begin
      mem_rd(.ptr(ral.buffer), .offset('h10 + i), .data(data));
      //USB device address location
      set_dev_addr = data[30:24];
    end

    //Set the new USB device address
    csr_wr(.ptr(ral.usbctrl), .value({9'h0, set_dev_addr, 16'h0001}));

    // Transaction to new USB device address
    trans_to_new_dev_addrs(set_dev_addr, .ack_invalid(1'b0));

    // Transaction to non-configured USB device address.
    // Should timeout after 18-bit USB clocks as device will not ack.
    set_dev_addr = 7'h5;
    trans_to_new_dev_addrs(set_dev_addr, .ack_invalid(1'b1));
  endtask

  // Transaction to new USB device address
  task trans_to_new_dev_addrs(bit [6:0] dev_addr_l, bit ack_invalid);
    // Configure out transaction
    configure_out_trans();

    // Out token packet followed by a data packet
    call_token_seq_to_set_addr(PidTypeOutToken, .dev_addr(dev_addr_l));
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    // Delay to make sure all status are updated after transaction.
    cfg.clk_rst_vif.wait_clks(10);

    // Get response from DUT
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    if (ack_invalid)
      `DV_CHECK_EQ(cfg.m_usb20_agent_cfg.time_out, 1)
    else
      `DV_CHECK_EQ(m_usb20_item.m_pid_type, PidTypeAck);
  endtask

  virtual task call_token_seq_to_set_addr(input pid_type_e pid_type, input bit [6:0] dev_addr);
    `uvm_create_on(m_token_pkt, p_sequencer.usb20_sequencer_h)
    m_token_pkt.m_pkt_type = PktTypeToken;
    m_token_pkt.m_pid_type = pid_type;
    assert(m_token_pkt.randomize() with {m_token_pkt.address == dev_addr;
                                         m_token_pkt.endpoint inside {4'b0};});
    m_usb20_item = m_token_pkt;
    start_item(m_token_pkt);
    finish_item(m_token_pkt);
  endtask

endclass
