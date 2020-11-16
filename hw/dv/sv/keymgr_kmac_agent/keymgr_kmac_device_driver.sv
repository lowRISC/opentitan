// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_device_driver extends keymgr_kmac_driver;
  `uvm_component_utils(keymgr_kmac_device_driver)
  `uvm_component_new


  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    super.run_phase(phase);
  endtask

  // reset signals
  virtual task reset_signals();
    invalidate_signals();
  endtask

  virtual function void invalidate_signals();
    cfg.vif.device_cb.rsp_done          <= 0;
    cfg.vif.device_cb.rsp_digest_share0 <= 'x;
    cfg.vif.device_cb.rsp_digest_share1 <= 'x;
    cfg.vif.device_cb.rsp_error         <= 'x;
  endfunction

  // drive trans received from sequencer
  virtual task get_and_drive();
    forever begin
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_HIGH)

      repeat (rsp.rsp_delay) begin
        if (cfg.vif.rst_n) @(cfg.vif.device_cb);
      end

      cfg.vif.device_cb.rsp_done          <= 1;
      cfg.vif.device_cb.rsp_digest_share0 <= rsp.rsp_digest_share0;
      cfg.vif.device_cb.rsp_digest_share1 <= rsp.rsp_digest_share1;
      cfg.vif.device_cb.rsp_error         <= rsp.rsp_error;

      if (cfg.vif.rst_n) @(cfg.vif.device_cb);
      invalidate_signals();

      `uvm_info(`gfn, "item sent", UVM_HIGH)
      seq_item_port.item_done(rsp);
    end
  endtask

endclass
