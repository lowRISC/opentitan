// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class keymgr_sanity_vseq extends keymgr_base_vseq;
  `uvm_object_utils(keymgr_sanity_vseq)
  `uvm_object_new

  // test op at StReset
  constraint do_op_before_init_c {
    do_op_before_init == 1;
  }

  task body();
    `uvm_info(`gfn, "Key manager sanity check", UVM_HIGH)
    // check operation at StInit state
    keymgr_operations(.advance_state(0), .num_gen_op(1), .clr_output(1));
    // Advance state until StDisabled. In each state check SW output and clear output
    repeat (5) begin
      keymgr_operations(.advance_state(1), .num_gen_op(1), .clr_output(1));
    end

  endtask : body

endclass : keymgr_sanity_vseq
