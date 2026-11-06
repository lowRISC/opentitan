// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Driver that sends OTP key responses. There is no response sent back to the sequence and any item
// is discarded on reset.

class otp_key_driver extends dv_base_driver #(otp_key_rsp_seq_item, otp_key_agent_cfg);
  `uvm_component_utils(otp_key_driver)

  // Port that sends generated request items. This should be connected to an instance of
  // otp_key_sequencer, which can use it to trigger items in a reactive response sequence. The items
  // from that sequence will come back to this driver.
  uvm_analysis_port#(otp_key_req_seq_item) m_req_port;

  extern function new (string name, uvm_component parent);
  extern virtual task run_phase(uvm_phase phase);

  // Get items from the sequencer and drive them. This task is declared in dv_base_driver.
  extern virtual task get_and_drive();

  // React to a reset. This task is declared in dv_base_driver.
  extern virtual task on_enter_reset();

  // Drive a single item (sending a response)
  extern local task drive_item(otp_key_rsp_seq_item item);

  // Monitor the request signals and generate items for m_req_port
  //
  // This works by running take_reqs_between_resets whenever not in reset.
  extern local task take_reqs();

  // Monitor the request signals and generate items for m_req_port
  //
  // This runs between resets and is killed by the caller when a reset is asserted.
  extern local task take_reqs_between_resets();

  // Wait the given number of cycles, returning early on a reset
  //
  // This waits with @(cfg.m_vif.host_cb), ensuring that the timing lines up with the clocking block
  // drives in drive_item.
  extern local task wait_cycles_or_reset(int unsigned num_cycles);
endclass

function otp_key_driver::new (string name, uvm_component parent);
  super.new(name, parent);
  m_req_port = new("m_req_port", this);
endfunction

task otp_key_driver::run_phase(uvm_phase phase);
  fork
    super.run_phase(phase);
    take_reqs();
  join_none
endtask

task otp_key_driver::get_and_drive();
  forever begin
    seq_item_port.get_next_item(req);
    drive_item(req);
  end
endtask

task otp_key_driver::on_enter_reset();
  cfg.m_vif.host_cb.data_ack   <= 1'b0;
  cfg.m_vif.host_cb.addr_ack   <= 1'b0;
  cfg.m_vif.host_cb.key        <= 'x;
  cfg.m_vif.host_cb.rand_key   <= 'x;
  cfg.m_vif.host_cb.seed_valid <= 'x;
endtask

task otp_key_driver::drive_item(otp_key_rsp_seq_item item);
  // Check that m_req is not null (giving a helpful error if it is)
  if (item.m_req == null) `uvm_fatal("null_req", "Response item with a null request.")

  // If the item has a delay of a positive number of cycles, wait that long before asserting ack.
  wait_cycles_or_reset(item.m_delay_cycles);

  // If we are not now in reset, drive the signal values to the clocking block
  if (cfg.m_vif.rst_ni) begin
    cfg.m_vif.host_cb.data_ack   <= item.m_req.m_is_data_req;
    cfg.m_vif.host_cb.addr_ack   <= ~item.m_req.m_is_data_req;
    cfg.m_vif.host_cb.key        <= item.m_key;
    cfg.m_vif.host_cb.rand_key   <= item.m_rand_key;
    cfg.m_vif.host_cb.seed_valid <= item.m_seed_valid;
  end

  // Assert the ack for a single cycle
  wait_cycles_or_reset(1);

  // Clear the ack signals immediately in the clocking block (whether or not there has been a reset)
  cfg.m_vif.host_cb.data_ack   <= 0;
  cfg.m_vif.host_cb.addr_ack   <= 0;

  // Unless there is a reset (or one has already happened), keep everything stable for another 62
  // cycles. This matches an explicit stability guarantee in the otp_ctrl specification.
  wait_cycles_or_reset(62);

  // Clear the other response signals in the clocking block before returning.
  cfg.m_vif.host_cb.key        <= 'x;
  cfg.m_vif.host_cb.rand_key   <= 'x;
  cfg.m_vif.host_cb.seed_valid <= 'x;

  // We can finally report that the item is done. Note that the ack might have been 62 cycles ago,
  // but it "locked" the interface for the following cycles.
  seq_item_port.item_done();
endtask

task otp_key_driver::take_reqs();
  wait(!$isunknown(cfg.m_vif.rst_ni));
  forever begin
    wait(cfg.m_vif.rst_ni);
    fork : isolation_fork begin
      fork
        take_reqs_between_resets();
        wait(!cfg.m_vif.rst_ni);
      join_any
      disable fork;
    end join
  end
endtask

task otp_key_driver::take_reqs_between_resets();
  bit old_data_req, old_addr_req;
  forever begin
    // This is implementing $rose(...) on two values inside a clocking block, which isn't natively
    // supported on the main target EDA tool. Instead, we look for edges in the signals by taking an
    // "old" value and using XOR.
    //
    // The protocol description in the otp_ctrl documentation doesn't explicitly describe whether
    // back-to-back requests (which would stop posedge detection from working) are possible. Either
    // way, we definitely don't expect rram_ctrl to make multiple requests of either type after a
    // reset, so there are assertions in otp_key_if that check that the req signals drop after an
    // ack. This guarantees that there will be a posedge on any new request.
    wait ((cfg.m_vif.host_cb.req.data_req ^ old_data_req) ||
          (cfg.m_vif.host_cb.req.addr_req ^ old_addr_req));


    if (cfg.m_vif.host_cb.req.data_req & ~old_data_req) begin
      otp_key_req_seq_item data_req_item = otp_key_req_seq_item::type_id::create("data_req_item");
      data_req_item.m_is_data_req = 1;
      m_req_port.write(data_req_item);
      old_data_req = 1;
    end

    if (cfg.m_vif.host_cb.req.addr_req & ~old_addr_req) begin
      otp_key_req_seq_item addr_req_item = otp_key_req_seq_item::type_id::create("addr_req_item");
      addr_req_item.m_is_data_req = 0;
      m_req_port.write(addr_req_item);
      old_addr_req = 1;
    end

    if (!cfg.m_vif.host_cb.req.data_req) old_data_req = 0;
    if (!cfg.m_vif.host_cb.req.addr_req) old_addr_req = 0;

    @(cfg.m_vif.host_cb);
  end
endtask

task otp_key_driver::wait_cycles_or_reset(int unsigned num_cycles);
  if (!num_cycles || !cfg.m_vif.rst_ni) return;

  fork : isolation_fork begin
    fork
      repeat (num_cycles) @(cfg.m_vif.host_cb);
      wait(!cfg.m_vif.rst_ni);
    join_any
    disable fork;
  end join
endtask
