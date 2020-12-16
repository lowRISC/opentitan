// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class keymgr_smoke_vseq extends keymgr_base_vseq;
  `uvm_object_utils(keymgr_smoke_vseq)
  `uvm_object_new

  // limit to SW operations
  constraint gen_operation_c {
    gen_operation inside {keymgr_pkg::OpGenId, keymgr_pkg::OpGenSwOut};
  }

  task body();
    `uvm_info(`gfn, "Key manager smoke check", UVM_HIGH)
    // Advance 6 times
    // StReset -> StCreatorRootKey -> StOwnerIntKey -> StOwnerIntKey -> StDisabled -> StDisabled
    // In each state check SW output and clear output
    repeat (6) begin
      keymgr_operations(.advance_state(1), .num_gen_op(1), .clr_output(1));
    end

  endtask : body

endclass : keymgr_smoke_vseq
