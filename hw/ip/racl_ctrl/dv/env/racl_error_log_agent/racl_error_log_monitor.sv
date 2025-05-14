// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A monitor for an error log interface

class racl_error_log_monitor extends dv_base_monitor #(.ITEM_T (racl_error_log_vec_item),
                                                       .REQ_ITEM_T (racl_error_log_vec_driver_item),
                                                       .RSP_ITEM_T (racl_error_log_vec_driver_item),
                                                       .CFG_T (racl_error_log_agent_cfg));
  `uvm_component_utils(racl_error_log_monitor)

  extern function new(string name, uvm_component parent);

  extern task run_phase(uvm_phase phase);
endclass

function racl_error_log_monitor::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

task racl_error_log_monitor::run_phase(uvm_phase phase);
  forever begin
    logic valid = 1'b0;

    // Monitor the interface on every clock edge when we are not in reset
    @(posedge cfg.vif.clk_i)
    if(!cfg.vif.rst_ni) continue;

    // Should we produce a sequence item? We only need one if there is at least one subscriber
    // reporting an error.
    for (int i = 0; i < 64; i++) if (cfg.vif.ctrl_cb.errors[i].valid) valid = 1'b1;
    if (valid) begin
      racl_error_log_vec_item item = racl_error_log_vec_item::type_id::create("item");

      for (int i = 0; i < 64; i++) begin
        if (cfg.vif.ctrl_cb.errors[i].valid) begin
          item.errors[i] = racl_error_log_item::type_id::create($sformatf("errors[%0d]", i));
          item.errors[i].overflow        = cfg.vif.ctrl_cb.errors[i].overflow;
          item.errors[i].role            = cfg.vif.ctrl_cb.errors[i].racl_role;
          item.errors[i].ctn_uid         = cfg.vif.ctrl_cb.errors[i].ctn_uid;
          item.errors[i].read_not_write  = cfg.vif.ctrl_cb.errors[i].read_access;
          item.errors[i].request_address = cfg.vif.ctrl_cb.errors[i].request_address;
        end
      end
      analysis_port.write(item);
    end
  end
endtask
