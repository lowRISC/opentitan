// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Max length out transaction_vseq
class usbdev_max_length_out_transaction_vseq extends usbdev_random_length_out_transaction_vseq;
  `uvm_object_utils(usbdev_max_length_out_transaction_vseq)

  `uvm_object_new

  usb20_item     m_usb20_item;
  RSP            rsp_item;
  rand bit [3:0] ep;
  bit            rand_or_not = 0;
  bit      [6:0] num_of_bytes = 64;
  bit      [6:0] data_size;
  bit      [4:0] buffer_id = 5'd1;

  constraint ep_c{
    ep inside {[0:11]};
  }

  task body();
    bit [6:0] rx_fifo_data_size;
    configure_trans();
    // Out token packet followed by a data packet of max bytes
    call_token_seq(PktTypeToken, PidTypeOutToken, ep);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    get_response(rsp_item);
    $cast(m_usb20_item, rsp_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    // Checking that data is of maximum length (64 bytes)
    csr_rd(.ptr(ral.rxfifo.size), .value(rx_fifo_data_size));
    `DV_CHECK_EQ(rx_fifo_data_size, num_of_bytes);
    // change available buffer id
    ral.avbuffer.buffer.set(buffer_id + 1);
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
    // Enable RX Out
    ral.rxenable_out[0].out[ep].set(1'b1);
    csr_update(ral.rxenable_out[0]);
    // set buffer id =1
    ral.avbuffer.buffer.set(buffer_id);
    csr_update(ral.avbuffer);
  endtask
endclass
