// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sysrst_ctrl_driver extends dv_base_driver #(.ITEM_T(sysrst_ctrl_item),
                                              .CFG_T (sysrst_ctrl_agent_cfg));
  `uvm_component_utils(sysrst_ctrl_driver)

  // the base class provides the following handles for use:
  // sysrst_ctrl_agent_cfg: cfg

  `uvm_component_new

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    super.run_phase(phase);
  endtask

  // reset signals
  virtual task reset_signals();
   cfg.vif.ac_present <= 0;
   cfg.vif.key0_in <= 0;
   cfg.vif.key1_in <= 0;
   cfg.vif.key2_in <= 0;
   cfg.vif.pwrb_in <= 0;
   cfg.vif.lid_open <= 0;
   cfg.vif.ec_rst_l_in <= 1;
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
    forever begin
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_NONE)
       drive_input();
      `uvm_info(`gfn, "item sent", UVM_HIGH)
      seq_item_port.item_done(rsp);
    end
  endtask

  //Drive input pins
  virtual task drive_input();
   @(posedge cfg.vif.clk_i)
   cfg.vif.driver_cb.ac_present <= req.ac_present;
   cfg.vif.driver_cb.key0_in <= req.key0_in;
   cfg.vif.driver_cb.key1_in <= req.key1_in;
   cfg.vif.driver_cb.key2_in <= req.key2_in;
   cfg.vif.driver_cb.pwrb_in <= req.pwrb_in;
   cfg.vif.driver_cb.lid_open <= req.lid_open;
   cfg.vif.driver_cb.ec_rst_l_in <= req.ec_rst_l_in;
  endtask

endclass
