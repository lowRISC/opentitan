// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_out_iso_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_out_iso_vseq)

  `uvm_object_new

  task body();
    bit pkt_received;
    uvm_reg_data_t rxfifo;
    super.dut_init("HARD");
    clear_all_interrupts();
    cfg.clk_rst_vif.wait_clks(10);
    configure_out_trans();
    cfg.clk_rst_vif.wait_clks(10);
    csr_wr(.ptr(ral.out_iso[0].iso[endp]),  .value(1'b1)); // ISO EP OUT
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(10);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    cfg.clk_rst_vif.wait_clks(20);
    ral.avoutbuffer.buffer.set(out_buffer_id + 1);
    csr_update(ral.avoutbuffer);
    csr_rd(.ptr(ral.intr_state.pkt_received), .value(pkt_received));
    // DV_CHECK on pkt_received interrupt
    `DV_CHECK_EQ(pkt_received, 1)
    csr_rd(.ptr(ral.rxfifo), .value(rxfifo));
    csr_wr(.ptr(ral.intr_state), .value(32'h0001_ffff));
  endtask

  // Overide the base class method to handle isochronous transfer
  task call_data_seq(input pkt_type_e pkt_type, input pid_type_e pid_type,
    input bit rand_or_not, input bit [6:0] num_of_bytes);
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    m_data_pkt.m_pkt_type = pkt_type;
    m_data_pkt.m_pid_type = pid_type;
    m_data_pkt.m_usb_transfer = usb_transfer_e'(IsoTrans);  // Defines Transfer types
    if (rand_or_not) assert(m_data_pkt.randomize());
    else assert(m_data_pkt.randomize() with {m_data_pkt.data.size() == num_of_bytes;});
    m_usb20_item = m_data_pkt;
    start_item(m_data_pkt);
    finish_item(m_data_pkt);
  endtask
endclass
