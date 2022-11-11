// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_device_driver extends csrng_driver;
  `uvm_component_utils(csrng_device_driver)
  `uvm_component_new

  uint   cmd_ack_dly;
  bit    rsp_sts;

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    super.run_phase(phase);
  endtask

  virtual task reset_signals();
    cfg.vif.cmd_rsp_int.csrng_rsp_ack <= 1'b0;
    cfg.vif.cmd_rsp_int.csrng_rsp_sts <= 1'b0;
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
    wait (cfg.under_reset == 0);
    forever begin
      seq_item_port.get_next_item(req);
      `uvm_info(`gfn, $sformatf("Received item: %s", req.convert2string()), UVM_HIGH)
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
          cmd_ack_dly, cmd_ack_dly inside {cfg.min_cmd_ack_dly, cfg.max_cmd_ack_dly};)
      `DV_SPINWAIT_EXIT(
          repeat(cmd_ack_dly) @(cfg.vif.device_cb);
          cfg.vif.device_cb.cmd_rsp_int.csrng_rsp_ack <= 1'b1;
          `DV_CHECK_STD_RANDOMIZE_FATAL(rsp_sts)
          cfg.vif.device_cb.cmd_rsp_int.csrng_rsp_sts <= rsp_sts;
          @(cfg.vif.device_cb);
          cfg.vif.device_cb.cmd_rsp_int.csrng_rsp_ack <= 1'b0;
          cfg.vif.device_cb.cmd_rsp_int.csrng_rsp_sts <= 1'b0;,
          wait (cfg.under_reset == 1);)

      // Write ack bit again in case the race condition with `reset_signals`.
      if (cfg.under_reset) cfg.vif.device_cb.cmd_rsp_int.csrng_rsp_ack <= 1'b0;

      `uvm_info(`gfn, cfg.under_reset ? "item sent during reset" : "item sent", UVM_HIGH)
      seq_item_port.item_done(rsp);
    end
  endtask

endclass
