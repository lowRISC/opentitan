// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Out stall vseq
class usbdev_out_stall_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_out_stall_vseq)

  `uvm_object_new

  task body();
    // Configure out transaction
    configure_out_trans(ep_default);
    // Set out_stall endpoint
    ral.out_stall[0].endpoint[ep_default].set(1'b1);
    csr_update(ral.out_stall[0]);
    // Out token packet followed by a data packet
    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    check_response_matches(PidTypeStall);
  endtask
endclass
