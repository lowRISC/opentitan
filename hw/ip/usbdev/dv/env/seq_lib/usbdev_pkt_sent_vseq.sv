// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_pkt_sent test vseq
class usbdev_pkt_sent_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_pkt_sent_vseq)

  `uvm_object_new

  virtual task body();
    uvm_reg_data_t read_rxfifo;

     super.dut_init("HARD");
     // Clear interrupts
     csr_wr(.ptr(ral.intr_state), .value(32'h0001_ffff));

    // OUT TRANS
    // -------------------------------
    // Configure out transaction
    configure_out_trans();
    // Enable pkt_sent interrupt
    ral.intr_enable.pkt_sent.set(1'b1);
    csr_update(ral.intr_enable);

    // Out token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    // Get response from DUT
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);

    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    // Make sure buffer is availabe for next trans
    ral.avbuffer.buffer.set(set_buffer_id + 1);
    csr_update(ral.avbuffer);

    // IN TRANS
    // --------------------------------
    // Configure in transaction
    num_of_bytes = m_data_pkt.data.size();
    configure_in_trans();
    // Token pkt followed by handshake pkt
    call_token_seq(PktTypeToken, PidTypeInToken, endp);
    // Get response from DUT
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_data_pid_from_device(m_usb20_item, PidTypeData0);
    cfg.clk_rst_vif.wait_clks(20);
    call_handshake_sequence(PktTypeHandshake, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);

    // Check transaction accuracy
    check_trans_accuracy();
    // Clear in_sent
    csr_wr(.ptr(ral.in_sent[0]), .value(32'h0000_0fff));
    // Clear interrupts
    csr_wr(.ptr(ral.intr_state), .value(32'h0001_ffff));
  endtask

  task check_trans_accuracy();
    bit pkt_sent;
    // Read pkt_sent interrupt
    csr_rd(.ptr(ral.intr_state.pkt_sent), .value(pkt_sent));
    // DV_CHECK on pkt_sent interrupt
    `DV_CHECK_EQ(pkt_sent, 1);
  endtask

endclass
