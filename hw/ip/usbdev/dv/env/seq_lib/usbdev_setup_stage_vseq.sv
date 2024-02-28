// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_setup_stage test vseq
class usbdev_setup_stage_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_setup_stage_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t read_rxfifo;
    endp = 0;

    super.dut_init("HARD");
    clear_all_interrupts();
    // Configure setup transaction
    configure_setup_trans();

    // Setup token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeSetupToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    cfg.clk_rst_vif.wait_clks(20);

    // Get DUT response
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);

    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    // Make sure buffer is availabe for next trans
    ral.avsetupbuffer.buffer.set(setup_buffer_id + 1);
    csr_update(ral.avsetupbuffer);
  endtask

  // Overwrite call_data_seq as we want to send fixed data
  task call_data_seq(input pkt_type_e pkt_type, input pid_type_e pid_type,
                     input bit rand_or_not, input bit [6:0] num_of_bytes);
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    m_data_pkt.m_pkt_type = pkt_type;
    m_data_pkt.m_pid_type = pid_type;
    m_data_pkt.m_bmRT = bmrequesttype_e'(bmRequestType3);
    m_data_pkt.m_bR = brequest_e'(bRequestGET_DESCRIPTOR);
    // Send control data for GET_DESCRIPTOR
    m_data_pkt.set_payload (m_data_pkt.m_bmRT, m_data_pkt.m_bR,8'h00, 8'h01, 8'h00, 8'h00,
                            8'h40,8'h00);
    m_usb20_item = m_data_pkt;
    start_item(m_data_pkt);
    finish_item(m_data_pkt);
  endtask

endclass
