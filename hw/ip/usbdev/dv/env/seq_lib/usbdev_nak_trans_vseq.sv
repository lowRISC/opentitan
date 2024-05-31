// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_nak_trans test vseq
class usbdev_nak_trans_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_nak_trans_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t rx_enable;
    uvm_reg_data_t read_rxfifo;
    bit            rx_enable_out;

    // Configure transaction
    configure_out_trans(ep_default);
    // Set nak_out
    ral.set_nak_out[0].enable[ep_default].set(1'b1);
    csr_update(ral.set_nak_out[0]);

    // Out token packet followed by a data packet
    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));

    // Check first transaction accuracy
    check_response_matches(PidTypeAck);

    // Read rxenable_out
    csr_rd(.ptr(ral.rxenable_out[0]), .value(rx_enable));
    csr_update(ral.rxenable_out[0]);
    // Get rxenable_out.out[0] status
    rx_enable_out = bit'(get_field_val(ral.rxenable_out[0].out[0], rx_enable));
    `DV_CHECK_EQ(rx_enable_out, 0);

    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    // Make sure buffer is available for next trans
    csr_wr(.ptr(ral.avoutbuffer.buffer), .value(out_buffer_id + 1));

    // Out token packet followed by a data packet
    send_prnd_out_packet(ep_default, PidTypeData1, .randomize_length(1'b1), .num_of_bytes(0));

    // Check second transaction accuracy
    check_response_matches(PidTypeNak);
  endtask

endclass
