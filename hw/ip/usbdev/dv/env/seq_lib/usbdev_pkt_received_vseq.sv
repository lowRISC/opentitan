// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_pkt_received test vseq
class usbdev_pkt_received_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_pkt_received_vseq)

  `uvm_object_new

  task body();
    // Configure transaction
    configure_out_trans();
    // Enable pkt_received interrupt
    ral.intr_enable.pkt_received.set(1'b1);
    csr_update(ral.intr_enable);

    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    cfg.clk_rst_vif.wait_clks(10);
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);

    // Check that the USB device received a packet with the expected properties.
    check_pkt_received(endp, 0, out_buffer_id, m_data_pkt.data);
  endtask

endclass
