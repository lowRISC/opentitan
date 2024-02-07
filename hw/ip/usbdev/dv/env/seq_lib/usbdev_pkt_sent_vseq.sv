// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_pkt_sent test vseq
class usbdev_pkt_sent_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_pkt_sent_vseq)

  `uvm_object_new

  rand bit [3:0] endp;
  bit      [4:0] set_buffer_id = 5'd1;
  bit      [6:0] num_of_bytes = 8;
  bit            rand_or_not = 0;

   constraint endpoint_c {
    endp inside {[0:11]};
  }

  virtual task body();
    usb20_item     item;
    RSP            rsp_item;
    uvm_reg_data_t read_rxfifo;

    // OUT TRANS
    // -------------------------------
    // Configure out transaction
    configure_out_trans();
    // Out token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    get_response(rsp_item);
    $cast(item, rsp_item);
    get_out_response_from_device(item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);

    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    // Make sure buffer is availabe for next trans
    ral.avbuffer.buffer.set(set_buffer_id + 1);
    csr_update(ral.avbuffer);

    // IN TRANS
    // -------------------------------
    // Configure in transaction
    configure_in_trans();
    // Token pkt followed by handshake pkt
    call_token_seq(PktTypeToken, PidTypeInToken, endp);
    get_response(rsp_item);
    $cast(item, rsp_item);
    get_data_pid_from_device(item, PidTypeData0);
    cfg.clk_rst_vif.wait_clks(20);
    call_handshake_sequence(PktTypeHandshake, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);

    // Check transaction accuracy
    check_trans_accuracy();
    // Clear in_sent
    csr_wr(.ptr(ral.in_sent[0]), .value(32'h0000_0fff));
    // clear interrupts
    csr_wr(.ptr(ral.intr_state), .value(32'h0001_ffff));
  endtask

  task configure_out_trans();
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
    // Enable pkt_sent interrupt
    ral.intr_enable.pkt_sent.set(1'b1);
    csr_update(ral.intr_enable);
    // Available buffer id
    ral.avbuffer.buffer.set(set_buffer_id);
    csr_update(ral.avbuffer);
  endtask

  task configure_in_trans();
    // Enable Endp IN
    csr_wr(.ptr(ral.ep_in_enable[0].enable[endp]),  .value(1'b1));
    csr_update(ral.ep_in_enable[0]);
    // Configure IN Transaction
    ral.configin[endp].rdy.set(1'b1);
    csr_update(ral.configin[endp]);
    ral.configin[endp].size.set(num_of_bytes);
    csr_update(ral.configin[endp]);
    ral.configin[endp].buffer.set(set_buffer_id);
    csr_update(ral.configin[endp]);
  endtask

  task check_trans_accuracy();
    bit pkt_sent;
    // Read pkt_sent interrupt
    csr_rd(.ptr(ral.intr_state.pkt_sent), .value(pkt_sent));
    // DV_CHECK on pkt_sent interrupt
    `DV_CHECK_EQ(pkt_sent, 1);
  endtask

endclass
