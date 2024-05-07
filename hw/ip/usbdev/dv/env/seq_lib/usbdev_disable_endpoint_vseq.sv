// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_disable_endpoint_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_disable_endpoint_vseq)

  `uvm_object_new

  task body();
    // Configure OUT transaction
    configure_out_trans();

    // disable EP
    csr_wr(.ptr(ral.ep_out_enable[0].enable[endp]), .value(1'b0));
    csr_wr(.ptr(ral.ep_in_enable[0].enable[endp]), .value(1'b0));

    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));

    // Get response from DUT
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);

    // Haven't not got any response (as endpoint is disable) from DUT so it should timeout.
    `DV_CHECK_EQ(cfg.m_usb20_agent_cfg.time_out, 1)

    // Check the pkt reception status
    check_out_trans();

    // Configure in transaction
    configure_in_trans(out_buffer_id, m_data_pkt.data.size());

    // Token pkt followed by handshake pkt
    call_token_seq(PidTypeInToken);
    inter_packet_delay();
    // Send ACK just to ensure complete IN transaction.
    // After complete IN transaction it should be ignored (as endpoint is disable).
    call_handshake_sequence(PktTypeHandshake, PidTypeAck);

    // Adding a delay to ensures that the status are updated following the transaction.
    cfg.clk_rst_vif.wait_clks(4);

    // Check the pkt sent status
    check_in_trans();
  endtask

  task check_out_trans();
    bit pkt_received;
    // Get pkt_received interrupt status
    csr_rd(.ptr(ral.intr_state.pkt_received), .value(pkt_received));
    // DV_CHECK on pkt_received interrupt
    `DV_CHECK_EQ(pkt_received, 0);
  endtask

  task check_in_trans();
    bit pkt_sent;
    // Get pkt_sent interrupt status
    csr_rd(.ptr(ral.intr_state.pkt_sent), .value(pkt_sent));
    // DV_CHECK on pkt_received interrupt
    `DV_CHECK_EQ(pkt_sent, 0);
  endtask

endclass
