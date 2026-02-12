// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A monitor for an error log interface

class racl_error_log_monitor extends dv_base_monitor #(.ITEM_T (racl_error_log_vec_item),
                                                       .REQ_ITEM_T (racl_error_log_vec_driver_item),
                                                       .RSP_ITEM_T (racl_error_log_vec_driver_item),
                                                       .CFG_T (racl_error_log_agent_cfg));
  `uvm_component_utils(racl_error_log_monitor)

  // The interface that is monitored. This is set up by the agent in the build phase.
  virtual racl_error_log_if vif;

  extern function new(string name, uvm_component parent);

  extern task run_phase(uvm_phase phase);

  extern local task watch_resets();
  extern local task watch_logs();
endclass

function racl_error_log_monitor::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

task racl_error_log_monitor::run_phase(uvm_phase phase);
  if (vif == null) `uvm_fatal(`gfn, "No vif to monitor.")

  fork
    watch_resets();
    watch_logs();
  join
endtask

task racl_error_log_monitor::watch_resets();
  forever begin
    cfg.in_reset = 1'b1;
    wait(cfg.vif.rst_ni);
    cfg.in_reset = 1'b0;
    wait(!cfg.vif.rst_ni);
  end
endtask

task racl_error_log_monitor::watch_logs();
  forever begin
    logic valid = 1'b0;

    // Monitor the interface on every clock edge when we are not in reset
    @(vif.ctrl_cb)
    if(!vif.rst_ni) continue;

    // Should we produce a sequence item? We only need one if there is at least one subscriber
    // reporting an error.
    for (int i = 0; i < 64; i++) if (vif.ctrl_cb.errors[i].valid) valid = 1'b1;
    if (valid) begin
      racl_error_log_vec_item item = racl_error_log_vec_item::type_id::create("item");

      for (int i = 0; i < 64; i++) begin
        if (vif.ctrl_cb.errors[i].valid) begin
          item.errors[i] = racl_error_log_item::type_id::create($sformatf("errors[%0d]", i));
          item.errors[i].overflow        = vif.ctrl_cb.errors[i].overflow;
          item.errors[i].role            = vif.ctrl_cb.errors[i].racl_role;
          item.errors[i].ctn_uid         = vif.ctrl_cb.errors[i].ctn_uid;
          item.errors[i].read_not_write  = vif.ctrl_cb.errors[i].read_access;
          item.errors[i].request_address = vif.ctrl_cb.errors[i].request_address;
        end
      end
      analysis_port.write(item);
    end
  end
endtask
