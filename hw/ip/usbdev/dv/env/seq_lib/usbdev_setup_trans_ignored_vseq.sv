// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_setup_trans_ignored_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_setup_trans_ignored_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t rx_depth;
    bit pkt_received = 1;

    csr_wr(.ptr(ral.rxenable_setup[0].setup[ep_default]), .value(1'b0)); // Disable rx_enable setup
    csr_wr(.ptr(ral.ep_out_enable[0].enable[ep_default]), .value(1'b1)); // Enable OUT EP

    // Enable pkt_received interrupt
    ral.intr_enable.pkt_received.set(1'b1);
    csr_update(ral.intr_enable);

    // Send a randomized SETUP packet to the selected endpoint.
    send_prnd_setup_packet(ep_default);
    // An ignored SETUP packet shall receive no response.
    check_no_response();

    csr_rd(.ptr(ral.intr_state.pkt_received), .value(pkt_received));
    // Verify the packet received bit is zero.
    // That ensures that device ignored the setup transaction.
    `DV_CHECK_EQ(0, pkt_received);

    // Belt'n'braces - check that the RX FIFO is empty.
    csr_rd(.ptr(ral.usbstat.rx_depth), .value(rx_depth));
    `DV_CHECK_EQ(rx_depth, 0);
  endtask
endclass
