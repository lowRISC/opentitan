// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This driver sends items that represent requests to KMAC

class kmac_app_host_driver extends dv_base_driver #(.ITEM_T (kmac_app_req_item),
                                                    .CFG_T (kmac_app_agent_cfg));
  `uvm_component_utils(kmac_app_host_driver)

  extern function new(string name, uvm_component parent);

  // Consume items from the sequencer and drive them (task from dv_base_driver)
  extern task get_and_drive();

  // Called when entering reset (task from dv_base_driver)
  extern task on_enter_reset();

  // Send the request item in req, exiting early on reset
  extern local task send_req();
endclass

function kmac_app_host_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

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
  if (cfg.in_reset) return;

  // Clear the values in the clocking block again (so that they will be cleared in the interface on
  // the next clock edge unless there is another request).
  cfg.vif.host_cb.req_valid <= 0;
  cfg.vif.host_cb.data_s0   <= 'x;
  cfg.vif.host_cb.data_s1   <= 'x;
  cfg.vif.host_cb.strb      <= 'x;
  cfg.vif.host_cb.req_last  <= 'x;
endtask
