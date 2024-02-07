// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// rx fifo vseq
class usbdev_rx_fifo_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_rx_fifo_vseq)

  `uvm_object_new

  usb20_item         m_usb20_item;
  RSP                rsp_item;
  rand bit    [3:0]  ep;
  bit                rand_or_not = 0;
  bit         [6:0]  num_of_bytes = 4;
  bit         [31:0] actual_data;
  bit         [4:0]  buffer_id = 5'd1;
  uvm_reg_data_t     read_rxfifo;
  byte unsigned      expected_data[];
  typedef bit [31:0] exp_data_result;
  exp_data_result    data_array;


  task body();
    configure_trans();
    // Out token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, ep);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    cfg.clk_rst_vif.wait_clks(20);
    get_response(rsp_item);
    $cast(m_usb20_item, rsp_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    // change available buffer id
    ral.avbuffer.buffer.set(buffer_id + 1);
    csr_update(ral.avbuffer);
    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    `uvm_info(`gfn, $sformatf("Rxfifo = %h", read_rxfifo), UVM_DEBUG)
    // Read data from buffer memory
    mem_rd(.ptr(ral.buffer), .offset('h10), .data(actual_data));
    `uvm_info(`gfn, $sformatf("Actual Data = %h", actual_data), UVM_DEBUG)
    // Checking the expected data and actual data
    expected_data = m_data_pkt.data;
    expected_data = {>>8{expected_data}};
    expected_data = {<<{expected_data}};
    data_array = exp_data_result'(expected_data);
    `uvm_info(`gfn, $sformatf("Expected Data = %h", data_array), UVM_DEBUG)
    `DV_CHECK_EQ(data_array, actual_data);
  endtask

  task configure_trans();
    super.apply_reset("HARD");
    super.dut_init("HARD");
    cfg.clk_rst_vif.wait_clks(200);
    // clear interrupts
    csr_wr(.ptr(ral.intr_state), .value(32'h0001_ffff));
    // Enable EP0 Out
    csr_wr(.ptr(ral.ep_out_enable[0].enable[ep]), .value(1'b1));
    csr_update(ral.ep_out_enable[0]);
    // Enable RX Out
    ral.rxenable_out[0].out[ep].set(1'b1);
    csr_update(ral.rxenable_out[0]);
    // set buffer id = 1
    ral.avbuffer.buffer.set(buffer_id);
    csr_update(ral.avbuffer);
  endtask
endclass
