// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class key_sideload_driver#(
    parameter type KEY_T = keymgr_pkg::hw_key_req_t
) extends dv_base_driver #(.ITEM_T(key_sideload_item#(KEY_T)),
                           .CFG_T (key_sideload_agent_cfg#(KEY_T)));
  `uvm_component_utils(key_sideload_driver#(KEY_T))

  // the base class provides the following handles for use:
  // key_sideload_agent_cfg: cfg

  `uvm_component_new

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    super.run_phase(phase);
  endtask

  // reset signals
  virtual task reset_signals();
    cfg.vif.sideload_key.valid = 0;
    cfg.vif.sideload_key.key[0] = 'x;
    cfg.vif.sideload_key.key[1] = 'x;
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
    forever begin
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_HIGH)
      cfg.vif.sideload_key.valid = req.valid;
      if (req.valid) begin
        cfg.vif.sideload_key.key[0] = req.key0;
        cfg.vif.sideload_key.key[1] = req.key1;
      end
      else begin
        cfg.vif.sideload_key.key[0] = 'x;
        cfg.vif.sideload_key.key[1] = 'x;
      end
      // Always wait for one clock cycle. Otherwise, this task may consume zero time while the
      // reset is active. This would be problematic as it would cause the key sideload interface
      // to be updated endlessly and the DV environment to hang.
      cfg.vif.wait_clks(1);
      // send rsp back to seq
      `uvm_info(`gfn, "item sent", UVM_HIGH)
      cfg.vif.wait_clks_or_rst(req.rsp_delay);
      seq_item_port.item_done(req);
    end
  endtask

endclass
