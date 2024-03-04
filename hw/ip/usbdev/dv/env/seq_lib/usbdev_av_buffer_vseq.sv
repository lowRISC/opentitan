// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_av_buffer test vseq
class usbdev_av_buffer_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_av_buffer_vseq)

  `uvm_object_new

  usb20_item      item;
  RSP             rsp_item;
  bit      [6:0]  num_of_bytes = 8;

  task pre_start();
    super.pre_start();
    rand_or_not = 1'b0;
  endtask

  task body();
    // Configure transaction
    configure_trans();
    // Out token packet followed by a data packet of 8 bytes
    call_token_seq(PidTypeOutToken);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PidTypeData0, rand_or_not, num_of_bytes);
    get_response(rsp_item);
    $cast(item, rsp_item);
    get_out_response_from_device(item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    // Check transaction accuracy
    check_trans_accuracy();
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
    ral.avoutbuffer.buffer.set(out_buffer_id);
    csr_update(ral.avoutbuffer);
  endtask

  task check_trans_accuracy();
    bit         [31:0] read_data_1;
    bit         [31:0] read_data_2;
    typedef bit [63:0] expected_data;
    byte unsigned      exp_byte_data[];
    expected_data      exp_data;
    uvm_reg_data_t     read_rxfifo;
    int unsigned       offset;

    // Calculate start address (in 32-bit words) of buffer
    offset = out_buffer_id * 'h10;

    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    // Read buffer
    mem_rd(.ptr(ral.buffer), .offset(offset), .data(read_data_1));
    mem_rd(.ptr(ral.buffer), .offset(offset + 1), .data(read_data_2));
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
