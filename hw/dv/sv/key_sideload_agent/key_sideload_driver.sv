// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class key_sideload_driver#(
    parameter type KEY_T = keymgr_pkg::hw_key_req_t
) extends dv_base_driver #(.ITEM_T(key_sideload_item#(KEY_T)),
                           .CFG_T (key_sideload_agent_cfg#(KEY_T)));
  `uvm_component_param_utils(key_sideload_driver#(KEY_T))

  // the base class provides the following handles for use:
  // key_sideload_agent_cfg: cfg

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction

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
      cfg.vif.sideload_key.key[0] = req.valid ? req.key0 : 'x;
      cfg.vif.sideload_key.key[1] = req.valid ? req.key1 : 'x;
      `uvm_info(`gfn, "item sent", UVM_HIGH)

      cfg.vif.wait_clks_or_rst(1 + req.rsp_delay);

      seq_item_port.item_done(req);
    end
  endtask

endclass
