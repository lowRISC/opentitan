// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_base_vseq extends cip_base_vseq #(
    .RAL_T               (ac_range_check_reg_block),
    .CFG_T               (ac_range_check_env_cfg),
    .COV_T               (ac_range_check_env_cov),
    .VIRTUAL_SEQUENCER_T (ac_range_check_virtual_sequencer)
  );
  `uvm_object_utils(ac_range_check_base_vseq)

  // Various knobs to enable certain routines
  bit do_ac_range_check_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_ac_range_check_init) ac_range_check_init();
  endtask

  virtual task dut_shutdown();
    // Check for pending ac_range_check operations and wait for them to complete
    // TODO MVy: probably useless, TBC
  endtask

  // Setup basic ac_range_check features
  virtual task ac_range_check_init();
    `uvm_error(`gfn, "FIXME")
  endtask

endclass : ac_range_check_base_vseq
