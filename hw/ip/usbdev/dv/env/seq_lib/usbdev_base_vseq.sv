// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_base_vseq extends cip_base_vseq #(
  .CFG_T               (usbdev_env_cfg),
  .RAL_T               (usbdev_reg_block),
  .COV_T               (usbdev_env_cov),
  .VIRTUAL_SEQUENCER_T (usbdev_virtual_sequencer)
);
`uvm_object_utils(usbdev_base_vseq)

usb20_item     m_usb20_item;
RSP            m_response_item;
token_pkt      m_token_pkt;
data_pkt       m_data_pkt;
handshake_pkt  m_handshake_pkt;
sof_pkt        m_sof_pkt;
rand bit [3:0] endp;
// Current SETUP buffer number
bit [4:0] setup_buffer_id = 5'd1;
// Current OUT buffer number
bit [4:0] out_buffer_id = 5'd7;
// Current IN buffer number
bit [4:0] in_buffer_id = 5'd13;
bit      [6:0] num_of_bytes;
bit            rand_or_not = 1'b1;

constraint endpoint_c {
  endp inside {[0:11]};
}
// various knobs to enable certain routines
bit do_usbdev_init = 1'b1;

// add post_reset_delays for sync between bus clk and usb clk in the apply_reset task
bit apply_post_reset_delays_for_sync = 1'b1;

`uvm_object_new

// Override apply_reset to cater to AON domain as well.
virtual task apply_reset(string kind = "HARD");
  fork
    if (kind == "HARD" || kind == "BUS_IF") begin
      super.apply_reset("HARD");
    end

    if (kind == "HARD") begin
      cfg.aon_clk_rst_vif.apply_reset();
    end
  join
  do_apply_post_reset_delays_for_sync();
endtask

virtual task apply_resets_concurrently(int reset_duration_ps = 0);
  cfg.aon_clk_rst_vif.drive_rst_pin(0);
  super.apply_resets_concurrently(cfg.aon_clk_rst_vif.clk_period_ps);
  cfg.aon_clk_rst_vif.drive_rst_pin(1);
endtask

// Apply additional delays at the dut_init stage when either apply_reset or
// wait_for_reset is called. The additional delays allow the logic to sync
// across clock domains so that the Dut behaves deterministically. To disable
// this, set apply_post_reset_delays_for_sync in the extended class' pre_start.
virtual task do_apply_post_reset_delays_for_sync();
  if (apply_post_reset_delays_for_sync) begin
    fork
      cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));
      cfg.aon_clk_rst_vif.wait_clks($urandom_range(5, 10));
    join
  end
endtask

// Override wait_for_reset to cater to AON domain as well.
virtual task wait_for_reset(string reset_kind     = "HARD",
  bit wait_for_assert   = 1,
  bit wait_for_deassert = 1);

  fork
    if (reset_kind == "HARD" || reset_kind == "BUS_IF") begin
      super.wait_for_reset(reset_kind, wait_for_assert, wait_for_deassert);
    end
    if (reset_kind == "HARD") begin
      if (wait_for_assert) begin
        `uvm_info(`gfn, "waiting for aon rst_n assertion...", UVM_MEDIUM)
        @(negedge cfg.aon_clk_rst_vif.rst_n);
      end
      if (wait_for_deassert) begin
        `uvm_info(`gfn, "waiting for aon rst_n de-assertion...", UVM_MEDIUM)
        @(posedge cfg.aon_clk_rst_vif.rst_n);
      end
      `uvm_info(`gfn, "usbdev wait_for_reset done", UVM_HIGH)
    end
  join
  do_apply_post_reset_delays_for_sync();
endtask

// Override dut_init to do some basic usbdev initializations (if enabled).
virtual task dut_init(string reset_kind = "HARD");
  super.dut_init();
  if (do_usbdev_init) usbdev_init();
endtask

  virtual task call_token_seq(input pid_type_e pid_type);
    `uvm_create_on(m_token_pkt, p_sequencer.usb20_sequencer_h)
    m_token_pkt.m_pkt_type = PktTypeToken;
    m_token_pkt.m_pid_type = pid_type;
    assert(m_token_pkt.randomize() with {m_token_pkt.address inside {7'b0};
                                         m_token_pkt.endpoint == endp;});
    m_usb20_item = m_token_pkt;
    start_item(m_token_pkt);
    finish_item(m_token_pkt);
  endtask

  virtual task call_data_seq(input pkt_type_e pkt_type, input pid_type_e pid_type,
                             input bit rand_or_not, input bit [6:0] num_of_bytes);
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    m_data_pkt.m_pkt_type = pkt_type;
    m_data_pkt.m_pid_type = pid_type;
    if (rand_or_not) assert(m_data_pkt.randomize());
    else assert(m_data_pkt.randomize() with {m_data_pkt.data.size() == num_of_bytes;});
    m_usb20_item = m_data_pkt;
    start_item(m_data_pkt);
    finish_item(m_data_pkt);
  endtask

  virtual task get_out_response_from_device(usb20_item rsp_itm, input pid_type_e pid_type);
    `uvm_create_on(m_handshake_pkt, p_sequencer.usb20_sequencer_h)
    m_handshake_pkt.m_pid_type = pid_type;
    m_usb20_item = m_handshake_pkt;
    // DV_CHECK on device reponse
    `DV_CHECK_EQ(m_usb20_item.m_pid_type, rsp_itm.m_pid_type);
  endtask

  virtual task get_data_pid_from_device(usb20_item rsp_itm, input pid_type_e pid_type);
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    m_data_pkt.m_pid_type = pid_type;
    m_usb20_item = m_data_pkt;
    // DV_CHECK on device reponse
    `DV_CHECK_EQ(m_usb20_item.m_pid_type, rsp_itm.m_pid_type);
  endtask

  virtual task call_handshake_sequence(input pkt_type_e pkt_type, input pid_type_e pid_type);
    `uvm_create_on(m_handshake_pkt, p_sequencer.usb20_sequencer_h)
    m_handshake_pkt.m_pkt_type = pkt_type;
    m_handshake_pkt.m_pid_type = pid_type;
    m_usb20_item = m_handshake_pkt;
    start_item(m_handshake_pkt);
    finish_item(m_handshake_pkt);
  endtask

virtual task dut_shutdown();
  // check for pending usbdev operations and wait for them to complete
  // TODO
endtask

// setup basic usbdev features
virtual task usbdev_init(bit [TL_DW-1:0] device_address = 0);
  // Enable USBDEV
  ral.usbctrl.enable.set(1'b1);
  ral.usbctrl.device_address.set(device_address);
  csr_update(ral.usbctrl);
endtask

virtual task configure_out_trans();
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

virtual task configure_setup_trans();
  // Enable EP0 Out
  csr_wr(.ptr(ral.ep_out_enable[0].enable[endp]), .value(1'b1));
  csr_update(ral.ep_out_enable[0]);
  // Enable rx setup
  ral.rxenable_setup[0].setup[endp].set(1'b1);
  csr_update(ral.rxenable_setup[0]);
  // Set buffer
  ral.avsetupbuffer.buffer.set(setup_buffer_id);
  csr_update(ral.avsetupbuffer);
endtask

virtual task configure_in_trans(bit [4:0] buffer_id);
  // Enable Endp IN
  csr_wr(.ptr(ral.ep_in_enable[0].enable[endp]),  .value(1'b1));
  csr_update(ral.ep_in_enable[0]);
  // Configure IN Transaction
  ral.configin[endp].rdy.set(1'b1);
  csr_update(ral.configin[endp]);
  ral.configin[endp].size.set(num_of_bytes);
  csr_update(ral.configin[endp]);
  ral.configin[endp].buffer.set(buffer_id);
  csr_update(ral.configin[endp]);
endtask

virtual task call_sof_seq(input pkt_type_e pkt_type, input pid_type_e pid_type);
  `uvm_create_on(m_sof_pkt, p_sequencer.usb20_sequencer_h)
  m_sof_pkt.m_pkt_type = pkt_type;
  m_sof_pkt.m_pid_type = pid_type;
  assert(m_sof_pkt.randomize());
  m_usb20_item = m_sof_pkt;
  start_item(m_sof_pkt);
  finish_item(m_sof_pkt);
endtask
endclass : usbdev_base_vseq
