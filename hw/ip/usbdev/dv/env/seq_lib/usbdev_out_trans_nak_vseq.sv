// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// out_trans_nak vseq
class usbdev_out_trans_nak_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_out_trans_nak_vseq)

  `uvm_object_new

  usb20_item    m_usb20_item;
  RSP     rsp_item;
  rand bit [3:0] ep;
  bit            rand_or_not = 1;
  bit      [6:0] num_of_bytes;
  bit [4:0] buffer_id = 5'd1;

  constraint ep_c{
    ep inside {[0:11]};
  }

  task body();
    configure_trans();
    // Out token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, ep);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    cfg.clk_rst_vif.wait_clks(20);
    get_response(rsp_item);
    $cast(m_usb20_item, rsp_item);
    get_out_response_from_device(m_usb20_item, PidTypeNak);
    ral.avbuffer.buffer.set(buffer_id + 1); // change available buffer id
    csr_update(ral.avbuffer);
  endtask

  task configure_trans();
    super.apply_reset("HARD");
    super.dut_init("HARD");
    cfg.clk_rst_vif.wait_clks(200);
    // clear interrupts
    csr_wr(.ptr(ral.intr_state), .value(32'h0001_ffff));
    // Enable EP Out
    csr_wr(.ptr(ral.ep_out_enable[0].enable[ep]), .value(1'b1));
    csr_update(ral.ep_out_enable[0]);
    // Enable rx out
    ral.rxenable_out[0].out[ep].set(1'b0);
    csr_update(ral.rxenable_out[0]);
    // set buffer id =1
    ral.avbuffer.buffer.set(buffer_id);
    csr_update(ral.avbuffer);
  endtask
endclass
