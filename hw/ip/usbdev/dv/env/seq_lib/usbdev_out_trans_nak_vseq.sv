// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Out trans nak vseq
class usbdev_out_trans_nak_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_out_trans_nak_vseq)

  `uvm_object_new

  task body();
    super.dut_init("HARD");
    // Configure out transaction
    configure_out_trans();
    // Clear RX Out
    ral.rxenable_out[0].out[endp].set(1'b0);
    csr_update(ral.rxenable_out[0]);
    // Out token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    cfg.clk_rst_vif.wait_clks(20);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeNak);
  endtask
endclass
