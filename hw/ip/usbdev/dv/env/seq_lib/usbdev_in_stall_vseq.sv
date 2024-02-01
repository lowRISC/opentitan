// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_in_stall_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_in_stall_vseq)

  `uvm_object_new

  task body();
    // Configure IN endpoint with a zero-length packet for collection; packet length
    // does not matter since we're expecting to receive a STALL anyway.
    configure_in_trans(out_buffer_id, 0);
    csr_wr(.ptr(ral.in_stall[0].endpoint[endp]),  .value(1'b1)); // Stall EP IN
    // Token pkt followed by handshake pkt
    call_token_seq(PidTypeInToken);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeStall);
  endtask
endclass
