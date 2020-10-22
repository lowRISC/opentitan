// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class keymgr_sanity_vseq extends keymgr_base_vseq;
  `uvm_object_utils(keymgr_sanity_vseq)
  `uvm_object_new

  task body();
    `uvm_info(`gfn, "Key manager sanity check", UVM_HIGH)
    // Advance state until StDisabled. In each state check SW output and clear output
    keymgr_operations(.exp_next_state(keymgr_pkg::StCreatorRootKey), .gen_output(1), .clr_output(1));
    keymgr_operations(.exp_next_state(keymgr_pkg::StOwnerIntKey), .gen_output(1), .clr_output(1));
    keymgr_operations(.exp_next_state(keymgr_pkg::StOwnerKey), .gen_output(1), .clr_output(1));
    keymgr_operations(.exp_next_state(keymgr_pkg::StDisabled), .gen_output(1), .clr_output(1));
    keymgr_operations(.exp_next_state(keymgr_pkg::StDisabled), .gen_output(1), .clr_output(1));
  endtask : body

endclass : keymgr_sanity_vseq
