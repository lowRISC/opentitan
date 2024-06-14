// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// In data stage vseq
class usbdev_in_data_stage_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_in_data_stage_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t read_rxfifo;
    bit in_sent;
    rand_or_not = 0;
    super.dut_init("HARD");
    clear_all_interrupts();
    ral.intr_enable.pkt_sent.set(1'b1); // Enable pkt_sent interrupt
    csr_update(ral.intr_enable);

    // ------------------OUT TRANS----------------------
    // Configure out transaction
    configure_out_trans();
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
    ral.avoutbuffer.buffer.set(out_buffer_id + 1);
    csr_update(ral.avoutbuffer);

    // ------------------IN TRANS----------------------
    // Configure in transaction
    num_of_bytes = m_data_pkt.data.size();
    configure_in_trans(out_buffer_id);
    // Token pkt followed by handshake pkt
    call_token_seq(PktTypeToken, PidTypeInToken, endp);
    // Get response from DUT
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_data_pid_from_device(m_usb20_item, PidTypeData0);
    cfg.clk_rst_vif.wait_clks(20);
    call_handshake_sequence(PktTypeHandshake, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    check_in_trans_accuracy();
    // Write 1 to clear particular EPs in_sent
    csr_wr(.ptr(ral.in_sent[0].sent[endp]), .value(1'b1));
    csr_rd(.ptr(ral.in_sent[0].sent[endp]), .value(in_sent));
    `DV_CHECK_EQ(0, in_sent); // verify that after writing one in_sent bit is cleared.
  endtask

   task check_in_trans_accuracy();
    bit pkt_sent;
    bit sent;
    csr_rd(.ptr(ral.intr_state.pkt_sent), .value(pkt_sent));
    csr_rd(.ptr(ral.in_sent[0].sent[endp]), .value(sent));
    `DV_CHECK_EQ(1, pkt_sent);
    `DV_CHECK_EQ(1, sent);
  endtask

   // Overwrite call_data_seq as we want to send fixed data
  virtual task call_data_seq(input pkt_type_e pkt_type, input pid_type_e pid_type,
    input bit rand_or_not, input bit [6:0] num_of_bytes);
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    m_data_pkt.m_pkt_type = pkt_type;
    m_data_pkt.m_pid_type = pid_type;
    m_data_pkt.m_bmRT = bmRequestType3;
    m_data_pkt.m_bR = bRequestGET_DESCRIPTOR;
    //Send standard device request GET_DESCRIPTOR
    if (rand_or_not)
      assert(m_data_pkt.randomize());
    else
      m_data_pkt.set_payload (m_data_pkt.m_bmRT, m_data_pkt.m_bR,8'h00, 8'h01, 8'h00, 8'h00,
                              8'h40,8'h00);
      m_usb20_item = m_data_pkt;
      start_item(m_data_pkt);
      finish_item(m_data_pkt);
  endtask
endclass
