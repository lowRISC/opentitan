// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Driver that sends OTP macro requests, acting as otp_ctrl.
//
// The driver finishes each item as soon as its request has been accepted, so the next request can
// be sent while earlier ones are still waiting for their responses. Responses come back in order,
// and each one is sent to the sequence that sent its request with put_response(). A request that
// is dropped or not answered because of a reset gets no response.

class otp_macro_driver extends dv_base_driver #(.ITEM_T     (otp_macro_req_seq_item),
                                                .CFG_T      (otp_macro_agent_cfg),
                                                .RSP_ITEM_T (otp_macro_rsp_seq_item));
  `uvm_component_utils(otp_macro_driver)

  extern function new (string name, uvm_component parent);

  // Send requests and collect responses. This task is declared in dv_base_driver.
  extern virtual task get_and_drive();

  // React to a reset. This task is declared in dv_base_driver.
  extern virtual task on_enter_reset();

  // Get items from the sequencer and send each request.
  extern local task send_requests();

  // Wait for responses and send each one back to the sequence that sent its request.
  extern local task collect_responses();

  // Wait for the item's delay, then present its request until it is accepted. accepted is false if
  // a reset arrived first.
  extern local task send_request(otp_macro_req_seq_item item, output bit accepted);

  // Present the request and wait until it is accepted. Killed by the caller on a reset.
  extern local task present_request(otp_macro_req_seq_item item);

  // Stop driving a request: valid is low and the other fields are unknown.
  extern local task drive_idle();

  // Wait the given number of cycles, returning early on a reset
  extern local task wait_cycles_or_reset(int unsigned num_cycles);

  // Requests that have been accepted but not answered yet, oldest first
  local otp_macro_req_seq_item m_pending[$];
endclass

function otp_macro_driver::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

task otp_macro_driver::get_and_drive();
  fork
    send_requests();
    collect_responses();
  join
endtask

task otp_macro_driver::on_enter_reset();
  drive_idle();
  m_pending.delete();
endtask

task otp_macro_driver::send_requests();
  forever begin
    bit accepted;

    // If the next request isn't ready yet, stop driving the last one while we wait for it.
    seq_item_port.try_next_item(req);
    if (req == null) begin
      drive_idle();
      seq_item_port.get_next_item(req);
    end

    send_request(req, accepted);
    if (accepted && cfg.m_vif.rst_ni) m_pending.push_back(req);
    seq_item_port.item_done();
  end
endtask

task otp_macro_driver::collect_responses();
  forever begin
    @(cfg.m_vif.host_cb iff cfg.m_vif.host_cb.rsp.rvalid);

    // The monitor reports a response with no request, so just ignore it here.
    if (m_pending.size() > 0) begin
      otp_macro_rsp_seq_item rsp = otp_macro_rsp_seq_item::type_id::create("rsp");
      rsp.m_req   = m_pending.pop_front();
      rsp.m_rdata = cfg.m_vif.host_cb.rsp.rdata;
      rsp.m_err   = cfg.m_vif.host_cb.rsp.err;
      rsp.set_id_info(rsp.m_req);
      seq_item_port.put_response(rsp);
    end
  end
endtask

task otp_macro_driver::send_request(otp_macro_req_seq_item item, output bit accepted);
  accepted = 1'b0;

  if (item.m_delay_cycles > 0) begin
    drive_idle();
    wait_cycles_or_reset(item.m_delay_cycles);
  end
  if (!cfg.m_vif.rst_ni) return;

  fork : isolation_fork begin
    fork
      begin
        present_request(item);
        accepted = 1'b1;
      end
      wait (!cfg.m_vif.rst_ni);
    join_any
    disable fork;
  end join
endtask

task otp_macro_driver::present_request(otp_macro_req_seq_item item);
  cfg.m_vif.host_cb.req <= '{valid: 1'b1,
                             cmd:   item.m_cmd,
                             size:  item.m_size,
                             addr:  item.m_addr,
                             wdata: item.m_wdata};

  // The request is accepted at a clock edge where the sampled request is valid and ready is high.
  do @(cfg.m_vif.host_cb);
  while (!(cfg.m_vif.host_cb.req.valid && cfg.m_vif.host_cb.rsp.ready));
endtask

task otp_macro_driver::drive_idle();
  cfg.m_vif.host_cb.req <= '{valid: 1'b0, cmd: cmd_e'('x), size: 'x, addr: 'x, wdata: 'x};
endtask

task otp_macro_driver::wait_cycles_or_reset(int unsigned num_cycles);
  if (!num_cycles || !cfg.m_vif.rst_ni) return;

  fork : isolation_fork begin
    fork
      repeat (num_cycles) @(cfg.m_vif.host_cb);
      wait (!cfg.m_vif.rst_ni);
    join_any
    disable fork;
  end join
endtask
