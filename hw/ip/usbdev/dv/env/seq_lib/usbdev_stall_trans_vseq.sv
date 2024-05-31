// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_stall_trans_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_stall_trans_vseq)

  `uvm_object_new

  task body();
    // Configure out transaction
    configure_out_trans(ep_default);
    // Set stall on endp
    csr_wr(.ptr(ral.out_stall[0].endpoint[ep_default]), .value(1'b1));

    // Out token packet followed by a data packet
    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));

    // Check that the DUT reponds with the PidTypeStall
    check_response_matches(PidTypeStall);
  endtask

endclass
