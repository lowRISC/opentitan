// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Stall_priority_over_nak vseq
class usbdev_stall_priority_over_nak_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_stall_priority_over_nak_vseq)

  `uvm_object_new

  task body();
    // Configure out transaction
    configure_out_trans(ep_default);
    // Set nak_out endpoint
    csr_wr(ral.set_nak_out[0].enable[ep_default], 1'b1);
    // Set out_stall endpoint
    csr_wr(ral.out_stall[0].endpoint[ep_default], 1'b1);
    // Out token packet followed by a data packet
    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    // Verify that the device responds with a Stall PID instead of a nak,
    // as Stall takes priority in this context.
    check_response_matches(PidTypeStall);
  endtask
endclass
