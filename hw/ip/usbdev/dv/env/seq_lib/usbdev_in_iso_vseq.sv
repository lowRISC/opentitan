// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_in_iso_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_in_iso_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t rxfifo;
    super.dut_init("HARD");
    clear_all_interrupts();
    cfg.clk_rst_vif.wait_clks(10);
    ral.intr_enable.pkt_sent.set(1'b1); // Enable pkt_sent interrupt
    csr_update(ral.intr_enable);
    configure_out_trans(); // register configurations for OUT Trans.
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck); // check OUT response
    cfg.clk_rst_vif.wait_clks(20);
    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(rxfifo));
    // Make sure buffer is availabe for next trans
    ral.avoutbuffer.buffer.set(out_buffer_id + 1);
    csr_update(ral.avoutbuffer);
    num_of_bytes = m_data_pkt.data.size();
    configure_in_trans(out_buffer_id);  // register configurations for IN Trans.
    csr_wr(.ptr(ral.in_iso[0].iso[endp]),  .value(1'b1)); // ISO EP1 OUT
    cfg.clk_rst_vif.wait_clks(20);
    // Token pkt followed by handshake pkt
    call_token_seq(PktTypeToken, PidTypeInToken, endp);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_data_pid_from_device(m_usb20_item, PidTypeData0);
    cfg.clk_rst_vif.wait_clks(20);
    // Verify Transaction reads register status and verifis that IN trans is successfull.
    check_trans_accuracy();
    csr_wr(.ptr(ral.in_sent[0].sent[endp]), .value(1'b1));
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
