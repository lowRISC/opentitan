// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Rx pid err vseq
class usbdev_rx_pid_err_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_rx_pid_err_vseq)

  `uvm_object_new

  task body();
    // Configure out transaction
    configure_out_trans();
    // Enable rx_pid_err interrupt
    csr_wr(.ptr(ral.intr_enable.rx_pid_err), .value(1'b1));
    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_data_seq(~PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    // In this check we are checking the rx pid error interrupt bit because we are sending wrong
    // data pid and after getting wrong pid the rx pid err bit should be raised.
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(IntrRxPidErr), 1'b1)
  endtask
endclass
