// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// out_stall vseq
class usbdev_out_stall_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_out_stall_vseq)

  `uvm_object_new

  task body();
    super.dut_init("HARD");
    cfg.clk_rst_vif.wait_clks(200);
    csr_wr(.ptr(ral.intr_state), .value(32'h0001_ffff));  // clear interrupts
    // Configure out transaction
    configure_out_trans();
    // Set out_stall endpoint
    ral.out_stall[0].endpoint[endp].set(1'b1);
    csr_update(ral.out_stall[0]);
    // Out token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    cfg.clk_rst_vif.wait_clks(20);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeStall);
    ral.avbuffer.buffer.set(set_buffer_id + 1); // change available buffer id
    csr_update(ral.avbuffer);
  endtask
endclass
