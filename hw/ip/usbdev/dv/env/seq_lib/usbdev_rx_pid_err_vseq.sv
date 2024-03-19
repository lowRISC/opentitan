// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Rx pid err vseq
class usbdev_rx_pid_err_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_rx_pid_err_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t read_rxfifo;

    // Configure out transaction
    configure_out_trans();
    // Enable av_empty interrupt
    csr_wr(.ptr(ral.intr_enable.rx_pid_err), .value(1'b1));
    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    // In this check we are checking the rx pid error interrupt bit because we are sending wrong
    // data pid and after getting wrong pid the rx pid err bit should be raised.
    check_rx_pid_err();
  endtask

  // Overwrite call_data_seq as we want to send invalid data pid
  virtual task call_data_seq(input pid_type_e pid_type,
                             input bit randomize_length, input bit [6:0] num_of_bytes);
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    m_data_pkt.m_pkt_type = PktTypeData;
    m_data_pkt.m_pid_type = ~pid_type;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_data_pkt,
                                   !randomize_length -> m_data_pkt.data.size() == num_of_bytes;)
    m_usb20_item = m_data_pkt;
    start_item(m_data_pkt);
    finish_item(m_data_pkt);
  endtask

  task check_rx_pid_err();
    bit pid_err;
    // Read rx_pid_err interrupt status
    csr_rd(.ptr(ral.intr_state.rx_pid_err), .value(pid_err));
    // DV_CHECK on rx_pid_err interrupt
    `DV_CHECK_EQ(pid_err, 1)
  endtask
endclass
