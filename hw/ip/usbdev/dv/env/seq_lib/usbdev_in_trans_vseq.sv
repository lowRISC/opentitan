// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_pkt_sent test vseq
class usbdev_in_trans_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_in_trans_vseq)

  `uvm_object_new

  virtual task body();
    int unsigned max_tries = 4;
    bit pkt_sent;
    bit in_sent;

    ral.intr_enable.pkt_sent.set(1'b1); // Enable pkt_sent interrupt
    csr_update(ral.intr_enable);
    // For IN transaction need to do first OUT transaction
    // to store data in buffer memory for read through IN.
    configure_out_trans(ep_default); // register configurations for OUT Trans.

    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    check_response_matches(PidTypeAck);

    check_rx_packet(ep_default, 1'b0, out_buffer_id, m_data_pkt.data);

    // Note: data should have been written into the current OUT buffer by the above transaction
    configure_in_trans(ep_default, out_buffer_id, m_data_pkt.data.size());

    // Attempt to collect IN DATA packet in response.
    send_token_packet(ep_default, PidTypeInToken);
    check_response_matches(PidTypeData0);
    // ACKnowledge successful reception of the IN DATA packet.
    send_handshake(PidTypeAck);

    // We need to wait a few clock cycles for the interrupt state to change.
    for (int unsigned try = 0; try < 4; try++) begin
      csr_rd(.ptr(ral.intr_state.pkt_sent), .value(pkt_sent));
      if (pkt_sent) break;
    end
    // `pkt_sent` interrupt should now be asserted...
    `DV_CHECK_EQ(pkt_sent, 1);
    // ... as should the bit for this endpoint within the 'in_sent' register.
    csr_rd(.ptr(ral.in_sent[0].sent[ep_default]), .value(in_sent));
    `DV_CHECK_EQ(in_sent, 1);

    // Write 1 to clear particular EP's bit in `in_sent`
    csr_wr(.ptr(ral.in_sent[0].sent[ep_default]), .value(1'b1));
    csr_rd(.ptr(ral.in_sent[0].sent[ep_default]), .value(in_sent));
    `DV_CHECK_EQ(0, in_sent); // verify that after writing, the in_sent bit is cleared.
  endtask
endclass
