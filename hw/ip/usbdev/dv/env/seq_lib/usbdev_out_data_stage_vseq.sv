// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_out_data_stage_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_out_data_stage_vseq)

  `uvm_object_new

  task body();
    super.dut_init("HARD");
    clear_all_interrupts();
    cfg.clk_rst_vif.wait_clks(20);
    // Configure transaction
    configure_out_trans(); // register configurations for OUT Trans.
    cfg.clk_rst_vif.wait_clks(20);
    // OUT token
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    rand_or_not = 0;
    // Control data of get_descriptor
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck); // check OUT response
    cfg.clk_rst_vif.wait_clks(200);
    // Check transaction accuracy
    check_trans_accuracy();
    // Make sure buffer is availabe for next trans
    ral.avoutbuffer.buffer.set(out_buffer_id + 1);
    csr_update(ral.avoutbuffer);
  endtask

  task check_trans_accuracy();
    bit pkt_received;
    uvm_reg_data_t read_rxfifo;
    uvm_reg_data_t intr_state;
    ral.intr_enable.pkt_received.set(1'b1);
    csr_update(ral.intr_enable);
    // Get pkt_received interrupt status
    csr_rd(.ptr(ral.intr_state.pkt_received), .value(pkt_received));
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    // DV_CHECK on pkt_received interrupt
    `DV_CHECK_EQ(pkt_received, 1);
  endtask

  // Overwrite call_data_seq as we want to send fixed data and fixed size data
  virtual task call_data_seq(input pkt_type_e pkt_type, input pid_type_e pid_type,
    input bit rand_or_not, input bit [6:0] num_of_bytes);
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    m_data_pkt.m_pkt_type = pkt_type;
    m_data_pkt.m_pid_type = pid_type;
    m_data_pkt.m_bmRT = bmrequesttype_e'(bmRequestType3);
    m_data_pkt.m_bR = brequest_e'(bRequestGET_DESCRIPTOR);
    //Send control data for GET_DESCRIPTOR
    if (rand_or_not)
      assert(m_data_pkt.randomize());
    else
      m_data_pkt.set_payload (m_data_pkt.m_bmRT, m_data_pkt.m_bR,8'h00, 8'h01, 8'h00, 8'h00,
                              8'h40,8'h00);
      m_usb20_item = m_data_pkt;
      start_item(m_data_pkt);
      finish_item(m_data_pkt);
  endtask
endclass
