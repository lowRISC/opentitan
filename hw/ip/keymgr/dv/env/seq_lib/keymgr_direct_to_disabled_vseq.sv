// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Issue operation OpDisable in any state and check it enters StDisabled correctly
class keymgr_direct_to_disabled_vseq extends keymgr_base_vseq;
  `uvm_object_utils(keymgr_direct_to_disabled_vseq)
  `uvm_object_new

  task body();
    `uvm_info(`gfn, "Start seq", UVM_HIGH)
    // Advance any state
    repeat ($urandom_range(0, 4)) begin
      keymgr_operations(.advance_state(1));
    end

    `uvm_info(`gfn, $sformatf("Directly go to Disabled from %0s", current_state.name), UVM_MEDIUM)
    ral.control.start.set(1'b1);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.control.operation,
                                   // All values not enumerated below behave the same as disable
                                   !(value inside {keymgr_pkg::OpAdvance,
                                                   keymgr_pkg::OpGenId,
                                                   keymgr_pkg::OpGenSwOut,
                                                   keymgr_pkg::OpGenHwOut});)
    ral.control.operation.set(keymgr_pkg::OpDisable);
    csr_update(.csr(ral.control));
    ral.control.start.set(1'b0);

    wait_op_done(.is_gen_output(0));
    `DV_CHECK_EQ(current_state, keymgr_pkg::StDisabled)

    // issue some random operations in StDisabled
    keymgr_operations();

  endtask : body

endclass : keymgr_direct_to_disabled_vseq
