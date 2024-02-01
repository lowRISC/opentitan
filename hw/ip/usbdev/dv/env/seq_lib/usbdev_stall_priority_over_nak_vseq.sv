// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Stall_priority_over_nak vseq
class usbdev_stall_priority_over_nak_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_stall_priority_over_nak_vseq)

  `uvm_object_new

  task body();
    // Configure out transaction
    configure_out_trans();
    // Set nak_out endpoint
    csr_wr(ral.set_nak_out[0].enable[endp], 1'b1);
    // Set out_stall endpoint
    csr_wr(ral.out_stall[0].endpoint[endp], 1'b1);
    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    // Verify that the device responds with a Stall PID instead of a nak,
    // as Stall takes priority in this context.
    get_out_response_from_device(m_usb20_item, PidTypeStall);
  endtask
endclass
