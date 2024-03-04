// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// rx fifo vseq
class usbdev_rx_fifo_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_rx_fifo_vseq)

  `uvm_object_new

  task body();
    num_of_bytes = 4;
    rand_or_not = 0;
    super.dut_init("HARD");
    // Configure out transaction
    configure_out_trans();
    // Out token packet followed by a data packet of 8 bytes
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    cfg.clk_rst_vif.wait_clks(20);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    // Verifies that the data read from the SRAM is the same data as sent to the device in the data packet of the OUT transaction.
    check_trans_accuracy();
  endtask

  task check_trans_accuracy();
    bit         [31:0] actual_data;
    uvm_reg_data_t     read_rxfifo;
    byte unsigned      expected_data[];
    typedef bit [31:0] exp_data_result;
    exp_data_result    data_array;

    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    `uvm_info(`gfn, $sformatf("Rxfifo = %h", read_rxfifo), UVM_DEBUG)
    // Read data from buffer memory
    mem_rd(.ptr(ral.buffer), .offset('h70), .data(actual_data));
    `uvm_info(`gfn, $sformatf("Actual Data = %h", actual_data), UVM_DEBUG)
    // Checking the expected data and actual data
    expected_data = m_data_pkt.data;
    expected_data = {>>8{expected_data}};
    expected_data = {<<{expected_data}};
    data_array = exp_data_result'(expected_data);
    `uvm_info(`gfn, $sformatf("Expected Data = %h", data_array), UVM_DEBUG)
    `DV_CHECK_EQ(data_array, actual_data);
  endtask
endclass
