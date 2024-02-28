// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_out_status_stage test vseq
class usbdev_out_status_stage_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_out_status_stage_vseq)

  `uvm_object_new

  virtual task body();
    uvm_reg_data_t read_rxfifo;
    num_of_bytes = 0;
    rand_or_not  = 0;

    super.dut_init("HARD");
    clear_all_interrupts();

    // OUT TRANS
    // --------------------------------
    // For IN transaction need to do first OUT transaction
    // to store data in buffer memory for read through IN.
    // Configure out transaction
    configure_out_trans();

    // Out token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    cfg.clk_rst_vif.wait_clks(20);

    // Get response from DUT
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));

    // IN TRANS
    // --------------------------------
    // Configure in transaction
    // Note: data should have been written into the current OUT buffer by the above transaction
    configure_in_trans(out_buffer_id);
    // Token pkt followed by handshake pkt
    call_token_seq(PktTypeToken, PidTypeInToken, endp);
    cfg.clk_rst_vif.wait_clks(20);

    // Get response from DUT
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_data_pid_from_device(m_usb20_item, PidTypeData0);
    cfg.clk_rst_vif.wait_clks(20);
    call_handshake_sequence(PktTypeHandshake, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);

    // Check transaction accuracy
    check_trans_accuracy();
  endtask

  task check_trans_accuracy();
    bit pkt_sent;
    // Read pkt_sent interrupt
    csr_rd(.ptr(ral.intr_state.pkt_sent), .value(pkt_sent));
    // DV_CHECK on pkt_sent interrupt
    `DV_CHECK_EQ(pkt_sent, 1);
  endtask

endclass
