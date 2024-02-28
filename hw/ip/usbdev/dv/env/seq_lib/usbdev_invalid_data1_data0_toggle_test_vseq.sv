// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Invalid data1 data0 toggle test vseq
class usbdev_invalid_data1_data0_toggle_test_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_invalid_data1_data0_toggle_test_vseq)

  `uvm_object_new

  task body();
    // Configure out transaction
    configure_out_trans();
    // Enable link_out_err interrupt
    csr_wr(.ptr(ral.intr_enable.link_out_err), .value(1'b1));
    // Out token packet followed by a data packet with random data size
    for (int i = 0; i < 2; i++) begin
      call_token_seq(PidTypeOutToken);
      inter_packet_delay();
      call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
      get_response(m_response_item);
      $cast(m_usb20_item, m_response_item);
      get_out_response_from_device(m_usb20_item, PidTypeAck);
    end
    // When back to back transaction is sent without toggling data PID, it will trigger a
    // "link out error" interrupt. DV_CHECK on link_out_err interrupt.
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(IntrLinkOutErr), 1'b1)
  endtask
endclass
