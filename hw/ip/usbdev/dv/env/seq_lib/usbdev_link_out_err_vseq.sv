// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_link_out_err_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_link_out_err_vseq)

  `uvm_object_new

  task body();
    // Configure transaction
    configure_out_trans();

    // Out token packet followed by a data packet with corrupted crc16
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);

    // Haven't not got any response from DUT so it should timeout.
    `DV_CHECK_EQ(cfg.m_usb20_agent_cfg.time_out, 1)

    // Verify that the link_out_err signal goes high after sending a data packet
    // with a corrupted CRC16.
    check_link_out_err();
  endtask

  // Override the call_data_seq task to corrupt the crc16
  task call_data_seq(input pid_type_e pid_type, input bit randomize_length,
                     input bit [6:0] num_of_bytes);
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    m_data_pkt.m_pkt_type = PktTypeData;
    m_data_pkt.m_pid_type = pid_type;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_data_pkt,
                                   !randomize_length -> m_data_pkt.data.size() == num_of_bytes;)
    m_data_pkt.crc16 = ~m_data_pkt.crc16;
    m_usb20_item = m_data_pkt;
    start_item(m_data_pkt);
    finish_item(m_data_pkt);
  endtask

  task check_link_out_err();
    bit link_out_error;
    // Read link_out_err interrupt status
    csr_rd(.ptr(ral.intr_state.link_out_err), .value(link_out_error));
    // DV_CHECK on link_out_err interrupt
    `DV_CHECK_EQ(link_out_error, 1)
  endtask

endclass
