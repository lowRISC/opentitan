// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_pkt_sent test vseq
class usbdev_in_trans_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_in_trans_vseq)

  `uvm_object_new

  virtual task body();
    uvm_reg_data_t rxfifo;
    bit in_sent;

    ral.intr_enable.pkt_sent.set(1'b1); // Enable pkt_sent interrupt
    csr_update(ral.intr_enable);
    // For IN transaction need to do first OUT transaction
    // to store data in buffer memory for read through IN.
    configure_out_trans(); // register configurations for OUT Trans.
    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck); // check OUT response
    cfg.clk_rst_vif.wait_clks(20);
    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(rxfifo));
    // Note: data should have been written into the current OUT buffer by the above transaction
    configure_in_trans(out_buffer_id, m_data_pkt.data.size());
    // Token pkt followed by handshake pkt
    call_token_seq(PidTypeInToken);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_data_pid_from_device(m_usb20_item, PidTypeData0);
    cfg.clk_rst_vif.wait_clks(20);
    call_handshake_sequence(PktTypeHandshake, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    // Verify Transaction reads register status and verifis that IN transtion is successfull.
    check_trans_accuracy();
    // Write 1 to clear particular EPs in_sent
    csr_wr(.ptr(ral.in_sent[0].sent[endp]), .value(1'b1));
    csr_rd(.ptr(ral.in_sent[0].sent[endp]), .value(in_sent));
    `DV_CHECK_EQ(0, in_sent); // verify that after writting one in_sent bit is cleared.
  endtask

  task check_trans_accuracy();
    bit pkt_sent;
    bit sent;
    csr_rd(.ptr(ral.intr_state.pkt_sent), .value(pkt_sent));
    csr_rd(.ptr(ral.in_sent[0].sent[endp]), .value(sent));
    `DV_CHECK_EQ(1, pkt_sent);
    `DV_CHECK_EQ(1, sent);
  endtask
endclass
