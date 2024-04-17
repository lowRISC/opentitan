// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Setup priority over stall response vseq
class usbdev_setup_priority_over_stall_response_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_setup_priority_over_stall_response_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t read_rxfifo;
    // Configuring endpoint 0 for stalling
    endp = 0;

    // Set out_stall endpoint
    csr_wr(ral.out_stall[0].endpoint[endp], 1'b1);
    // Set in_stall endpoint
    csr_wr(ral.in_stall[0].endpoint[endp], 1'b1);
    // Configure setup transaction
    configure_setup_trans();
    // Out token packet followed by a data packet
    call_token_seq(PidTypeSetupToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(7'b0));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    // Verifies that the out and in stall endpoint
    check_setup_priority_over_stall();
  endtask

  task check_setup_priority_over_stall();
    uvm_reg_data_t in_stall;
    uvm_reg_data_t out_stall;

    // Read out stall endpoint
    csr_rd(.ptr(ral.out_stall[endp]), .value(out_stall));
    // Read in stall endpoint
    csr_rd(.ptr(ral.in_stall[endp]), .value(in_stall));
    // DV_CHECK on out stall endpoint
    `DV_CHECK_EQ(out_stall, 0);
    // DV_CHECK on in stall endpoint
    `DV_CHECK_EQ(in_stall, 0);
  endtask
endclass
