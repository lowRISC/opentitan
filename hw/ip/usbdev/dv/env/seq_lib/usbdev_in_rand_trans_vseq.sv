// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_in_rand_trans_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_in_rand_trans_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t read_rxfifo;
    super.dut_init("HARD");
    void'($value$plusargs("num_of_bytes=%0d", num_of_bytes));
    void'($value$plusargs("rand_or_not=%0b", rand_or_not));
    // For IN transaction need to do first OUT transaction
    // to store data in buffer memory for read through IN.
    configure_out_trans(); // register configurations for OUT Trans.
    // Out token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    // call_data_sequence(PktTypeData, PidTypeData0);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck); // check OUT response
    cfg.clk_rst_vif.wait_clks(20);
    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    // Make sure buffer is availabe for next trans
    ral.avbuffer.buffer.set(set_buffer_id + 1);
    csr_update(ral.avbuffer);
    num_of_bytes = m_data_pkt.data.size();
    configure_in_trans();  // register configurations for IN Trans.
    // Token pkt followed by handshake pkt
    call_token_seq(PktTypeToken, PidTypeInToken, endp);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_data_pid_from_device(m_usb20_item, PidTypeData0);
    cfg.clk_rst_vif.wait_clks(20);
    call_handshake_sequence(PktTypeHandshake, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    check_trans_accuracy(); // Verify Transaction
    csr_wr(.ptr(ral.in_sent[0]), .value(32'h0000_0fff)); // Clear in_sent
    csr_wr(.ptr(ral.intr_state), .value(32'h0001_ffff)); // clear interrupts
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
