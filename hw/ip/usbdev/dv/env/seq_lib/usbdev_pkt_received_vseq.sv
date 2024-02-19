// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_pkt_received test vseq
class usbdev_pkt_received_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_pkt_received_vseq)

  `uvm_object_new

  task body();
    // Configure transaction
    configure_out_trans();
    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    cfg.clk_rst_vif.wait_clks(10);
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(10);
    // Check transaction accuracy
    check_trans_accuracy();
  endtask

  task check_trans_accuracy();
    uvm_reg_data_t intr_state;
    // Read intr_state reg
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    // DV_CHECK on pkt_received interrupt
    `DV_CHECK_EQ(get_field_val(ral.intr_state.pkt_received, intr_state), 1)
  endtask

endclass
