// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Random length out transaction vseq
class usbdev_random_length_out_transaction_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_random_length_out_transaction_vseq)

  `uvm_object_new

  usb20_item     m_usb20_item;
  RSP            rsp_item;
  token_pkt      m_token_pkt;
  data_pkt       m_data_pkt;
  handshake_pkt  m_handshake_pkt;
  rand bit [3:0] ep;
  bit            rand_or_not = 1;
  bit      [6:0] num_of_bytes;
  bit      [6:0] data_size;
  bit      [6:0] rx_fifo_data_size;
  bit      [4:0] buffer_id = 5'd1;

  constraint ep_c{
    ep inside {[0:11]};
  }

  task body();
    configure_trans();
    // Out token packet followed by a data packet of random bytes
    call_token_seq(PktTypeToken, PidTypeOutToken, ep);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    get_response(rsp_item);
    $cast(m_usb20_item, rsp_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    // Checking that data is of random length (0-64 bytes)
    csr_rd(.ptr(ral.rxfifo.size), .value(rx_fifo_data_size));
    `uvm_info(`gfn, $sformatf("RX fifo size =  %d", rx_fifo_data_size), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("Data size =  %d", super.m_data_pkt.data.size()), UVM_DEBUG)
    `DV_CHECK_EQ(rx_fifo_data_size, super.m_data_pkt.data.size());
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
