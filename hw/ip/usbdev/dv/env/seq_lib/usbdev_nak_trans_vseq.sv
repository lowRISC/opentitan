// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_nak_trans test vseq
class usbdev_nak_trans_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_nak_trans_vseq)

  `uvm_object_new

  usb20_item     item;
  RSP            rsp_item;
  rand bit [3:0] endp;
  bit      [4:0] set_buffer_id = 5'd1;

  constraint endpoint_c {
    endp inside {[0:11]};
  }

  task body();
    uvm_reg_data_t rx_enable;
    uvm_reg_data_t read_rxfifo;
    bit            rx_enable_out;
    bit            rand_or_not = 1;
    bit      [6:0] num_of_bytes;

    // Configure transaction
    configure_trans();
    // Out token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    cfg.clk_rst_vif.wait_clks(20);

    // Check first transaction accuracy
    check_first_trans_accuracy();
    cfg.clk_rst_vif.wait_clks(20);

    // Read rxenable_out
    csr_rd(.ptr(ral.rxenable_out[0]), .value(rx_enable));
    csr_update(ral.rxenable_out[0]);
    // Get rxenable_out.out[0] status
    rx_enable_out = bit'(get_field_val(ral.rxenable_out[0].out[0], rx_enable));
    `DV_CHECK_EQ(rx_enable_out, 0);

    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    // Make sure buffer is availabe for next trans
    ral.avbuffer.buffer.set(set_buffer_id + 1);
    csr_update(ral.avbuffer);

    // Out token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData1, rand_or_not, num_of_bytes);
    cfg.clk_rst_vif.wait_clks(20);

    // Check second transaction accuracy
    check_second_trans_accuracy();
    cfg.clk_rst_vif.wait_clks(20);
    // Make sure buffer is availabe for next trans
    ral.avbuffer.buffer.set(set_buffer_id + 2);
    csr_update(ral.avbuffer);
  endtask

  task configure_trans();
    super.apply_reset("HARD");
    super.dut_init("HARD");
    cfg.clk_rst_vif.wait_clks(20);
    // Clear interrupts
    csr_wr(.ptr(ral.intr_state), .value(32'h0001_ffff));
    // Enable EP0 Out
    csr_wr(.ptr(ral.ep_out_enable[0].enable[endp]), .value(1'b1));
    csr_update(ral.ep_out_enable[0]);
    // Enable rx out
    ral.rxenable_out[0].out[endp].set(1'b1);
    csr_update(ral.rxenable_out[0]);
    // Set nak_out
    ral.set_nak_out[0].enable[endp].set(1'b1);
    csr_update(ral.set_nak_out[0]);
    // Set buffer
    ral.avbuffer.buffer.set(set_buffer_id);
    csr_update(ral.avbuffer);
  endtask

  task check_first_trans_accuracy();
    get_response(rsp_item);
    $cast(item, rsp_item);
    get_out_response_from_device(item, PidTypeAck);
  endtask

  task check_second_trans_accuracy();
    get_response(rsp_item);
    $cast(item, rsp_item);
    get_out_response_from_device(item, PidTypeNak);
  endtask

endclass
