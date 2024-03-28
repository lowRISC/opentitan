// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_device_timeout_missing_host_handshake_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_device_timeout_missing_host_handshake_vseq)

  `uvm_object_new

   pid_type_e m_pid_type;

  virtual task body();
    bit [2:0] select_pkt;
    // --------------------------------------------------------------------------------
    // OUT data packet
    // --------------------------------------------------------------------------------
    // Configure out transaction
    configure_out_trans();

    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));

    // Get response from DUT
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    `DV_CHECK_EQ(m_usb20_item.m_pkt_type, PktTypeHandshake);
    `DV_CHECK_EQ(m_usb20_item.m_pid_type, PidTypeAck);

    // --------------------------------------------------------------------------------
    // Retrieve that data packet using an IN transaction.
    // --------------------------------------------------------------------------------
    // Configure in transaction
    // Note: data should have been written into the current OUT buffer by the above transaction
    configure_in_trans(out_buffer_id, m_data_pkt.data.size());
    // Adding a delay ensures that configin register status is updated.
    cfg.clk_rst_vif.wait_clks(4);
    // Send IN Token pkt and don't send the hand_shake pkt after it.
    call_token_seq(PidTypeInToken);
    inter_packet_delay();

    // Send random token pkt
    select_pkt = $urandom_range(0, 2);
    m_pid_type = (select_pkt == 0) ? PidTypeSetupToken :
                 (select_pkt == 1) ? PidTypeOutToken   :
                  PidTypeInToken;
    call_token_seq(m_pid_type);

    // Verify IN Transaction, read registers status
    check_in_trans(.rdy(1), .in_sent(0));

    // Send token pkt followed by handshake pkt
    call_token_seq(PidTypeInToken);
    inter_packet_delay();
    call_handshake_sequence(PktTypeHandshake, PidTypeAck);
    // Adding a delay ensures that the registers status are updated.
    cfg.clk_rst_vif.wait_clks(4);
    // Verify IN Transaction, read registers status
    check_in_trans(.rdy(0), .in_sent(1));
  endtask

  task check_in_trans(bit rdy, bit in_sent);
    bit rdy_status;
    bit in_sent_status;
    csr_rd(.ptr(ral.configin[endp].rdy), .value(rdy_status));
    csr_rd(.ptr(ral.in_sent[0].sent[endp]), .value(in_sent_status));
    `DV_CHECK_EQ(rdy, rdy_status);
    `DV_CHECK_EQ(in_sent, in_sent_status);
  endtask

endclass
