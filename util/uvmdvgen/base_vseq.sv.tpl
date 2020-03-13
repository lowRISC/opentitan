// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

% if is_cip:
class ${name}_base_vseq extends cip_base_vseq #(
% else:
class ${name}_base_vseq extends dv_base_vseq #(
% endif
% if has_ral:
    .RAL_T               (${name}_reg_block),
% endif
    .CFG_T               (${name}_env_cfg),
    .COV_T               (${name}_env_cov),
    .VIRTUAL_SEQUENCER_T (${name}_virtual_sequencer)
  );
  `uvm_object_utils(${name}_base_vseq)

  // various knobs to enable certain routines
  bit do_${name}_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_${name}_init) ${name}_init();
  endtask

  virtual task dut_shutdown();
    // check for pending ${name} operations and wait for them to complete
    // TODO
  endtask

  // setup basic ${name} features
  virtual task ${name}_init();
    `uvm_error(`gfn, "FIXME")
  endtask

endclass : ${name}_base_vseq
