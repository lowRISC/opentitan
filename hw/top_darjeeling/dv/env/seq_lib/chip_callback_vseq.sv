// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_callback_vseq extends cip_base_vseq #(
    .CFG_T               (chip_env_cfg),
    .RAL_T               (chip_reg_block),
    .COV_T               (chip_env_cov),
    .VIRTUAL_SEQUENCER_T (chip_virtual_sequencer)
  );

  `uvm_object_utils(chip_callback_vseq)
  `uvm_object_new

  virtual task pre_apply_reset();
    // Do nothing but can be overridden in closed source environment.
  endtask

  virtual task post_apply_reset(string reset_kind = "HARD");
    // Do nothing but can be overridden in closed source environment.
  endtask

  virtual task pre_dut_init();
    // Do nothing but can be overridden in closed source environment.
  endtask

  virtual task post_dut_init();
    // Do nothing but can be overridden in closed source environment.
  endtask
endclass
