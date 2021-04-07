// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_base_vseq extends cip_base_vseq #(
  .RAL_T              (adc_ctrl_reg_block),
  .CFG_T              (adc_ctrl_env_cfg),
  .COV_T              (adc_ctrl_env_cov),
  .VIRTUAL_SEQUENCER_T(adc_ctrl_virtual_sequencer)
);
  `uvm_object_utils(adc_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_adc_ctrl_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_adc_ctrl_init) adc_ctrl_init();
  endtask

  virtual task dut_shutdown();
    // check for pending adc_ctrl operations and wait for them to complete
    // TODO
  endtask

  // setup basic adc_ctrl features
  virtual task adc_ctrl_init();
    `uvm_info(`gfn, "Initializating adc_ctrl, nothing to do at the moment", UVM_MEDIUM)
  endtask  // adc_ctrl_init

  virtual task apply_reset(string kind = "HARD");
    if (kind == "HARD") begin
      cfg.clk_aon_rst_vif.apply_reset();
    end
    super.apply_reset(kind);
  endtask  // apply_reset

endclass : adc_ctrl_base_vseq
