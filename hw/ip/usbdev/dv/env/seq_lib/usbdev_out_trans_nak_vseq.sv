// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Out trans nak vseq
class usbdev_out_trans_nak_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_out_trans_nak_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t all_endpoints = {NEndpoints{1'b1}};
    // Configure out transaction
    configure_out_trans(ep_default);
    // Clear rx_enable_out bit for the selected OUT endpoint; enable OUT packets for all other
    // endpoints to be a bit more robusy.
    ral.rxenable_out.out.set(all_endpoints & ~(1 << ep_default));
    csr_update(ral.rxenable_out);
    // Out token packet followed by a data packet
    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    check_response_matches(PidTypeNak);
  endtask
endclass
