// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This driver sends items that represent requests to KMAC

class kmac_app_host_driver extends dv_base_driver #(.ITEM_T (kmac_app_req_item),
                                                    .CFG_T (kmac_app_agent_cfg));
  `uvm_component_utils(kmac_app_host_driver)

  // Publishes completed KMAC response items to downstream components
  uvm_analysis_port #(kmac_app_rsp_item) m_rsp_port;

  extern function new(string name, uvm_component parent);
  extern task run_phase(uvm_phase phase);

  // Consume items from the sequencer and drive them (task from dv_base_driver)
  extern task get_and_drive();

  // Called when entering reset (task from dv_base_driver)
  extern task on_enter_reset();

  // Send the request item in req, exiting early on reset
  extern local task send_req();

  // Collect response handshakes and publish completed response items
  extern local task collect_responses();

  // Capture the response fields from the interface into a response item
  extern local function kmac_app_rsp_item capture_response();
endclass

function kmac_app_host_driver::new(string name, uvm_component parent);
  super.new(name, parent);
  m_rsp_port = new("m_rsp_port", this);
endfunction

task kmac_app_host_driver::run_phase(uvm_phase phase);
  fork
    super.run_phase(phase);
    collect_responses();
  join
endtask

task kmac_app_host_driver::get_and_drive();
  forever begin
    seq_item_port.get_next_item(req);
    send_req();
    seq_item_port.item_done();
  end
endtask

task kmac_app_host_driver::on_enter_reset();
  cfg.vif.host_cb.req_valid <= 0;
  cfg.vif.host_cb.data_s0   <= 'x;
  cfg.vif.host_cb.data_s1   <= 'x;
  cfg.vif.host_cb.strb      <= 'x;
  cfg.vif.host_cb.req_last  <= 'x;
  cfg.vif.host_cb.rsp_ready <= 0;
endtask

function kmac_app_rsp_item kmac_app_host_driver::capture_response();
  kmac_app_rsp_item rsp_item = kmac_app_rsp_item::type_id::create("rsp_item");

  rsp_item.m_digest_s0 = cfg.vif.host_cb.rsp_digest_s0;
  rsp_item.m_digest_s1 = cfg.vif.host_cb.rsp_digest_s1;
  rsp_item.m_error     = cfg.vif.host_cb.rsp_error;
  rsp_item.m_finish    = cfg.vif.host_cb.rsp_finish;
  rsp_item.m_delay     = 0;
  return rsp_item;
endfunction

task kmac_app_host_driver::collect_responses();
  bit rsp_ready_q;
  bit rsp_pending;
  kmac_app_rsp_item rsp_item;

  forever begin
    cfg.vif.host_cb.rsp_ready <= 0;
    wait (!cfg.in_reset);
    cfg.rsp_ready_policy.reset();
    rsp_ready_q = 0;
    rsp_pending = 0;

    fork : isolation_fork
      begin
        wait (cfg.in_reset);
      end
      begin
        forever begin
          @(cfg.vif.host_cb);

          if (rsp_pending && rsp_ready_q && cfg.vif.host_cb.rsp_valid) begin
            m_rsp_port.write(rsp_item);
            rsp_pending = 0;
          end else if (cfg.vif.host_cb.rsp_valid && !rsp_pending) begin
            rsp_item = capture_response();
            rsp_pending = 1;
          end

          // Call the policy every cycle (even right after a handshake and while rsp_valid is low)
          // so that policies such as "always" can hold rsp_ready high without a one-cycle dip.
          rsp_ready_q = cfg.rsp_ready_policy.get_rsp_ready(
              cfg.vif.host_cb.rsp_valid,
              cfg.rsp_ready_pct,
              cfg.max_rsp_ready_delay);
          cfg.vif.host_cb.rsp_ready <= rsp_ready_q;
        end
      end
    join_any
    disable isolation_fork;
  end
endtask

task kmac_app_host_driver::send_req();
  // Wait for m_delay cycles before we respond
  cfg.vif.wait_cycles(req.m_delay);
  if (cfg.in_reset) return;

  // Set values on the interface and wait until KMAC is ready
  cfg.vif.host_cb.req_valid <= 1;
  cfg.vif.host_cb.data_s0 <= req.m_data_s0;
  cfg.vif.host_cb.data_s1 <= req.m_data_s1;
  cfg.vif.host_cb.strb <= (1 << req.m_num_bytes) - 1;
  cfg.vif.host_cb.req_last <= req.m_last;
  fork : isolation_fork begin
    fork
      wait (cfg.in_reset);
      begin
        do begin
          @(cfg.vif.host_cb);
        end while (!cfg.vif.host_cb.req_ready);
      end
    join_any
    disable fork;
  end join

  // If we are in reset, we are done. (Don't bother clearing up: that will be handled by
  // on_enter_reset anyway)
  if (cfg.in_reset) begin
    return;
  end

  // Clear the values in the clocking block again (so that they will be cleared in the interface on
  // the next clock edge unless there is another request).
  cfg.vif.host_cb.req_valid <= 0;
  cfg.vif.host_cb.data_s0   <= 'x;
  cfg.vif.host_cb.data_s1   <= 'x;
  cfg.vif.host_cb.strb      <= 'x;
  cfg.vif.host_cb.req_last  <= 'x;
endtask
