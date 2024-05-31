// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Out trans nak vseq
class usbdev_out_trans_nak_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_out_trans_nak_vseq)

  `uvm_object_new

  task body();
    // Configure out transaction
    configure_out_trans(ep_default);
    // Clear RX Out
    ral.rxenable_out[0].out[ep_default].set(1'b0);
    csr_update(ral.rxenable_out[0]);
    // Out token packet followed by a data packet
    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    check_response_matches(PidTypeNak);
  endtask
endclass
