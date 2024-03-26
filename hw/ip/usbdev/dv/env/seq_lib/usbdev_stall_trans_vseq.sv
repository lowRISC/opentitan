// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_stall_trans_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_stall_trans_vseq)

  `uvm_object_new

  task body();
    // Configure out transaction
    configure_out_trans();
    // Set stall on endp
    csr_wr(.ptr(ral.out_stall[0].endpoint[endp]), .value(1'b1));

    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));

    // Check that the DUT reponds with the PidTypeStall
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    `DV_CHECK_EQ(m_usb20_item.m_pkt_type, PktTypeHandshake);
    `DV_CHECK_EQ(m_usb20_item.m_pid_type, PidTypeStall);
  endtask

endclass
