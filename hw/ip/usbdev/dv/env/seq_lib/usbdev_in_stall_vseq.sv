// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_in_stall_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_in_stall_vseq)

  `uvm_object_new

  task body();
    super.dut_init("HARD");
    clear_all_interrupts();
    cfg.clk_rst_vif.wait_clks(10);
    configure_in_trans(out_buffer_id);  // register configurations for IN Trans.
    csr_wr(.ptr(ral.in_stall[0].endpoint[endp]),  .value(1'b1)); // Stall EP IN
    csr_update(ral.in_stall[0]);
    // Token pkt followed by handshake pkt
    call_token_seq(PktTypeToken, PidTypeInToken, endp);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_data_pid_from_device(m_usb20_item, PidTypeStall);
    cfg.clk_rst_vif.wait_clks(20);
    // Set avbuffer id
    ral.avoutbuffer.buffer.set(out_buffer_id + 1);
    csr_update(ral.avoutbuffer);
  endtask
endclass
