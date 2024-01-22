// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class usbdev_smoke_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_smoke_vseq)

  `uvm_object_new

  usb20_item    m_usb20_item;
  usb20_item    rsp_itm;
  token_pkt     m_token_pkt;
  data_pkt      m_data_pkt;
  handshake_pkt m_handshake_pkt;

  task body();
    uvm_reg_data_t rx_fifo_read;
    uvm_reg_data_t rx_fifo_expected;
    uvm_reg_data_t rx_empty;
    uvm_reg_data_t usbstat;
    uvm_reg_data_t data;
    uvm_status_e status;
    bit [4:0] buffer_id = 5'd1;
    super.apply_reset("HARD");
    super.dut_init("HARD");
    cfg.clk_rst_vif.wait_clks(200);
    csr_wr(.ptr(ral.intr_state), .value(32'h0001_ffff));  // clear interrupts
    csr_wr(.ptr(ral.ep_out_enable[0].enable[0]), .value(1'b1)); // Enable EP0 Out
    csr_update(ral.ep_out_enable[0]);
    ral.rxenable_setup[0].setup[0].set(1'b1); // Enable rx setup
    csr_update(ral.rxenable_setup[0]);
    ral.avbuffer.buffer.set(buffer_id); // set buffer id =1
    csr_update(ral.avbuffer);
    ral.intr_enable.pkt_received.set(1'b1); // Enable pkt_received interrupt
    csr_update(ral.intr_enable);
    // Setup token packet followed by a data packet of 8 bytes
    call_token_sequence(PktTypeToken, PidTypeSetupToken);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_sequence(PktTypeData, PidTypeData0);
    cfg.clk_rst_vif.wait_clks(20);
    // read rx_fifo register to check rcvd buffer id, endpoint number and type setup/out
    csr_rd(.ptr(ral.rxfifo), .value(rx_fifo_read));
    // expected value of rx_fifof reg is (32'h80801)[setup = 1, payload size = 8 bytes buffid = 1]
    rx_fifo_expected = 32'h80801;
    `DV_CHECK_EQ(rx_fifo_expected, rx_fifo_read);
    ral.avbuffer.buffer.set(buffer_id + 1); // change available buffer id
    csr_update(ral.avbuffer);
  endtask

  task call_token_sequence(input pkt_type_e pkt_type, input pid_type_e pid_type);
    RSP rsp_item;
    `uvm_create_on(m_token_pkt, p_sequencer.usb20_sequencer_h)
    m_token_pkt.m_pkt_type = pkt_type;
    m_token_pkt.m_pid_type = pid_type;
    assert(m_token_pkt.randomize() with {m_token_pkt.address inside {7'b0};
                                         m_token_pkt.endpoint inside {4'd0};});
      m_usb20_item = m_token_pkt;
      start_item(m_token_pkt);
      finish_item(m_token_pkt);
      if (pid_type == PidTypeInToken) begin
        get_response(rsp_item);
        $cast(rsp_itm, rsp_item);
        get_response_from_device(rsp_itm, PidTypeData1);
      end
  endtask

  task call_data_sequence(input pkt_type_e pkt_type, input pid_type_e pid_type);
    RSP rsp_item;
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    m_data_pkt.m_pkt_type = pkt_type;
    m_data_pkt.m_pid_type = pid_type;
    m_data_pkt.m_bmRT = bmRequestType3;
    m_data_pkt.m_bR = bRequestGET_DESCRIPTOR;
    assert(m_data_pkt.randomize());
    m_usb20_item = m_data_pkt;
    m_data_pkt.set_payload (m_data_pkt.m_bmRT, m_data_pkt.m_bR,8'h00, 8'h01, 8'h00, 8'h00,
                            8'h40,8'h00);
    start_item(m_data_pkt);
    finish_item(m_data_pkt);
    get_response(rsp_item);
    $cast(rsp_itm, rsp_item);
    get_response_from_device(rsp_itm, PidTypeAck);
  endtask

  task get_response_from_device(usb20_item rsp_itm, input pid_type_e pid_type);
    `uvm_create_on(m_handshake_pkt, p_sequencer.usb20_sequencer_h)
    m_handshake_pkt.m_pid_type = pid_type;
    m_usb20_item = m_handshake_pkt;
    // DV_CHECK on device reponse packet id
    `DV_CHECK_EQ(m_usb20_item.m_pid_type, rsp_itm.m_pid_type);
  endtask
endclass : usbdev_smoke_vseq
