// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Out stall vseq
class usbdev_out_stall_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_out_stall_vseq)

  `uvm_object_new

  task body();
    super.dut_init("HARD");
    cfg.clk_rst_vif.wait_clks(200);
    clear_all_interrupts();
    // Configure out transaction
    configure_out_trans();
    // Set out_stall endpoint
    ral.out_stall[0].endpoint[endp].set(1'b1);
    csr_update(ral.out_stall[0]);
    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    cfg.clk_rst_vif.wait_clks(20);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeStall);
  endtask
endclass
