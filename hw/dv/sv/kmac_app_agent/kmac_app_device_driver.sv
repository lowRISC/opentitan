// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_device_driver extends kmac_app_driver;
  `uvm_component_utils(kmac_app_device_driver)
  `uvm_component_new

  task on_enter_reset();
    invalidate_signals();
  endtask

  virtual function void invalidate_signals();
    cfg.vif.device_cb.rsp_valid         <= 0;
    cfg.vif.device_cb.rsp_digest_share0 <= 'x;
    cfg.vif.device_cb.rsp_digest_share1 <= 'x;
    cfg.vif.device_cb.rsp_error         <= 'x;
    cfg.vif.device_cb.rsp_finish        <= 'x;
  endfunction

  // drive trans received from sequencer
  virtual task get_and_drive();
    forever begin
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_HIGH)

      `DV_SPINWAIT_EXIT(repeat (rsp.rsp_delay) @(cfg.vif.device_cb);,
                        wait(!cfg.vif.rst_n))

      cfg.vif.device_cb.rsp_valid         <= 1;
      cfg.vif.device_cb.rsp_digest_share0 <= rsp.digest_s0;
      cfg.vif.device_cb.rsp_digest_share1 <= rsp.digest_s1;
      cfg.vif.device_cb.rsp_error         <= rsp.error;
      cfg.vif.device_cb.rsp_finish        <= 0;

      `DV_SPINWAIT_EXIT(@(cfg.vif.device_cb);,
                        wait(!cfg.vif.rst_n))
      invalidate_signals();

      `uvm_info(`gfn, "item sent", UVM_HIGH)
      seq_item_port.item_done(rsp);
    end
  endtask

endclass
