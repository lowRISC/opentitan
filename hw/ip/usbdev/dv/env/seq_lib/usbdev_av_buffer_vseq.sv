// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_av_buffer test vseq
class usbdev_av_buffer_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_av_buffer_vseq)

  `uvm_object_new

  usb20_item      item;
  RSP             rsp_item;
  bit      [4:0]  set_buffer_id = 5'd1;
  rand bit [3:0]  endp;
  bit      [6:0]  num_of_bytes = 8;
  bit             rand_or_not = 0;

  constraint endpoint_c {
    endp inside {[0:11]};
  }

  task body();
    // Configure transaction
    configure_trans();
    // Out token packet followed by a data packet of 8 bytes
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    get_response(rsp_item);
    $cast(item, rsp_item);
    get_out_response_from_device(item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    // Check transaction accuracy
    check_trans_accuracy();
    // Make sure buffer is availabe for nex trans
    ral.avoutbuffer.buffer.set(set_buffer_id + 1);
    csr_update(ral.avoutbuffer);
  endtask

  task configure_trans();
    super.apply_reset("HARD");
    super.dut_init("HARD");
    cfg.clk_rst_vif.wait_clks(200);
    // Enable EP0 Out
    csr_wr(.ptr(ral.ep_out_enable[0].enable[endp]), .value(1'b1));
    csr_update(ral.ep_out_enable[0]);
    // Enable rx out
    ral.rxenable_out[0].out[endp].set(1'b1);
    csr_update(ral.rxenable_out[0]);
    // Set buffer
    ral.avoutbuffer.buffer.set(set_buffer_id);
    csr_update(ral.avoutbuffer);
  endtask

  task check_trans_accuracy();
    bit         [31:0] read_data_1;
    bit         [31:0] read_data_2;
    typedef bit [63:0] expected_data;
    byte unsigned      exp_byte_data[];
    expected_data      exp_data;
    uvm_reg_data_t     read_rxfifo;

    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    // Read buffer
    mem_rd(.ptr(ral.buffer), .offset('h10), .data(read_data_1));
    mem_rd(.ptr(ral.buffer), .offset('h11), .data(read_data_2));
    // Expected data or data send to DUT
    exp_byte_data = m_data_pkt.data;
    // Bit streaming to compliance with usb protocol LSB--->MSB
    exp_byte_data = {>>8{exp_byte_data}};
    exp_byte_data = {<<{exp_byte_data}};
    exp_data = expected_data'(exp_byte_data);
    // `DV check on actual and exp data
    `DV_CHECK_EQ(exp_data, {read_data_2,read_data_1});
  endtask

endclass
