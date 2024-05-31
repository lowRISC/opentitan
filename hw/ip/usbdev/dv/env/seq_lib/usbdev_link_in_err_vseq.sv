// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_link_in_err_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_link_in_err_vseq)

  `uvm_object_new

  virtual task body();
    bit link_error;

    configure_out_trans(ep_default);
    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    check_response_matches(PidTypeAck);
    // Check that link_in_err interrupt is zero.
    csr_rd(.ptr(ral.intr_state.link_in_err), .value(link_error));
    `DV_CHECK_EQ(0, link_error);
    configure_in_trans(ep_default, out_buffer_id, m_data_pkt.data.size());
    send_token_packet(ep_default, PidTypeInToken);
    check_response_matches(PidTypeData0);
    // Send unexpected PID to USB device and device will assert link_in_err interrupt.
    // Expected pkt is ACK but send NYET packet.
    send_handshake(PidTypeNyet);
    // The 'link_in_err' interrupt will take a few cycles to be asserted.
    for (uint i = 0; i < 16; i++) begin
      csr_rd(.ptr(ral.intr_state.link_in_err), .value(link_error));
      if (link_error) break;
    end
    // Check link_in_err is asserted.
    `DV_CHECK_EQ(link_error, 1'b1, "link_in_err interrupt not asserted when expected")
  endtask
endclass
