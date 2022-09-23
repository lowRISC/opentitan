// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_xht_device_driver extends dv_base_driver #(
    .ITEM_T(entropy_src_xht_item),
    .CFG_T (entropy_src_xht_agent_cfg)
);

  `uvm_component_utils(entropy_src_xht_device_driver)
  `uvm_component_new

  virtual task reset_signals();
    forever begin
      @(negedge cfg.vif.rst_n);
      `uvm_info(`gfn, "Driver is under reset", UVM_DEBUG)
      cfg.vif.xht_cb.rsp <= ENTROPY_SRC_XHT_RSP_DEFAULT;
      @(posedge cfg.vif.rst_n);
      `uvm_info(`gfn, "Driver is out of reset", UVM_DEBUG)
    end
  endtask

  virtual task get_and_drive();
    forever begin
      @(cfg.vif.xht_cb);
      seq_item_port.try_next_item(req);
      if (req == null) begin
        cfg.vif.xht_cb.rsp.test_fail_hi_pulse <= 1'b0;
        cfg.vif.xht_cb.rsp.test_fail_lo_pulse <= 1'b0;
      end else begin
        cfg.vif.xht_cb.rsp <= req.rsp;
        seq_item_port.item_done(req);
      end
    end
  endtask

endclass
