// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_base_vseq extends cip_base_vseq #(
    .RAL_T               (entropy_src_reg_block),
    .CFG_T               (entropy_src_env_cfg),
    .COV_T               (entropy_src_env_cov),
    .VIRTUAL_SEQUENCER_T (entropy_src_virtual_sequencer)
  );
  `uvm_object_utils(entropy_src_base_vseq)

  // various knobs to enable certain routines
  bit  do_entropy_src_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_entropy_src_init) entropy_src_init();
  endtask

  virtual task dut_shutdown();
    // check for pending entropy_src operations and wait for them to complete
    // TODO
  endtask

  // setup basic entropy_src features
  virtual task entropy_src_init();

    cfg.efuse_es_sw_reg_en_vif.drive_pin(.idx(0), .val(cfg.efuse_es_sw_reg_en));
  endtask

endclass : entropy_src_base_vseq
