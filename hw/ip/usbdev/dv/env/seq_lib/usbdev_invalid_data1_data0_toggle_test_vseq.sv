// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Invalid data1 data0 toggle test vseq
class usbdev_invalid_data1_data0_toggle_test_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_invalid_data1_data0_toggle_test_vseq)

  `uvm_object_new

  task body();
    int i;
    bit link_out_err;
    uvm_reg_data_t read_rxfifo;

    super.dut_init("HARD");
    // clear interrupts
    clear_all_interrupts();
    // Configure out transaction
    configure_out_trans();
    // Enable link_out_err interrupt
    ral.intr_enable.link_out_err.set(1'b1);
    csr_update(ral.intr_enable);
    // Out token packet followed by a data packet
    for (i = 0; i < 6; i++) begin
      call_token_seq(PktTypeToken, PidTypeOutToken, endp);
      cfg.clk_rst_vif.wait_clks(20);
      call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
      cfg.clk_rst_vif.wait_clks(20);
      get_response(m_response_item);
      $cast(m_usb20_item, m_response_item);
      get_out_response_from_device(m_usb20_item, PidTypeAck);
      // Read rxfifo reg
      csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
      // Make sure buffer is availabe for next trans
      ral.avoutbuffer.buffer.set(out_buffer_id + i);
      csr_update(ral.avoutbuffer);
    end
    // Read link_out_err interrupt
    csr_rd(.ptr(ral.intr_state.link_out_err), .value(link_out_err));
    // DV_CHECK on link_out_err interrupt
    `DV_CHECK_EQ(link_out_err, 1);
    // Clear intr_state
    csr_wr(.ptr(ral.intr_state), .value(32'h0001_ffff));
  endtask
endclass
