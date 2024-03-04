// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_pkt_received test vseq
class usbdev_pkt_received_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_pkt_received_vseq)

  `uvm_object_new

  usb20_item     item;
  RSP            rsp_item;
  bit            rand_or_not = 1;
  bit      [6:0] num_of_bytes;
  bit            pkt_received;
  uvm_reg_data_t read_rxfifo;
  uvm_reg_data_t intr_state;

  task body();
    // Configure transaction
    configure_trans();
    // Out token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
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
    clear_all_interrupts();
    // Enable EP0 Out
    csr_wr(.ptr(ral.ep_out_enable[0].enable[endp]), .value(1'b1));
    csr_update(ral.ep_out_enable[0]);
    // Enable rx out
    ral.rxenable_out[0].out[endp].set(1'b1);
    csr_update(ral.rxenable_out[0]);
    // Set buffer
    ral.avoutbuffer.buffer.set(out_buffer_id);
    csr_update(ral.avoutbuffer);
    // Enable pkt_received interrupt
    ral.intr_enable.pkt_received.set(1'b1);
    csr_update(ral.intr_enable);
  endtask

  task check_trans_accuracy();
    // Read rx_fifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    // Read intr_state reg
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    // Get pkt_received interrupt status
    pkt_received = bit'(get_field_val(ral.intr_state.pkt_received, intr_state));
    // DV_CHECK on pkt_received interrupt
    `DV_CHECK_EQ(pkt_received, 1);
  endtask

endclass
