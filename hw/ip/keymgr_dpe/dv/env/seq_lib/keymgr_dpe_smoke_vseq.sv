// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class keymgr_dpe_smoke_vseq extends keymgr_dpe_base_vseq;
  `uvm_object_utils(keymgr_dpe_smoke_vseq)
  `uvm_object_new

  // limit to SW operations
  constraint gen_operation_c {
    gen_operation inside {
      keymgr_dpe_pkg::OpDpeGenHwOut,
      keymgr_dpe_pkg::OpDpeGenSwOut
    };
  }

  constraint set_policy_c {
    policy.allow_child == 1;
    policy.exportable == 0;
    policy.retain_parent == 1;
  }

  constraint initial_slot_vals_c {
    // for initial latch of OTP key src slot does not matter
    soft src_slot inside {[0:keymgr_dpe_pkg::DpeNumSlots-1]};
    soft dst_slot == 0;
  }

  task body();
    `uvm_info(`gfn, "Key Manager DPE Smoke Start", UVM_HIGH)
    /*
       This smoke test uses advances a key into each available key slot. This means that
       retain_parent needs to be set to 1 for the key policy.

       1. Advance from StWorkDpeReset to StWorkDpeAvailable state (latching OTP)
         - Check OTP key
         - Check dst slot values (scb)
       2. Make further advance calls
         - retain parent is set, so each advance is to a new dst slot
         - Generate SW/HW identity's
         - Check SW/HW output (scb)
         - Check dst slot values (scb)
    */
      for (int iter = 0; iter<keymgr_dpe_pkg::DpeNumSlots+1; iter++) begin
        // retain_parent == 0, for the latched OTP
        // so src_slot must == dst_slot
        if (iter == 1) begin
          src_slot = dst_slot;
        // retain_parent == 1, for further advances calls
        // so src_slot must != dst_slot
        end else if (iter > 1 & iter < keymgr_dpe_pkg::DpeNumSlots)  begin
          src_slot = dst_slot;
          dst_slot ++;
        end
        // boot_stage would be exhausted by the last slot
        // so src_slot must != the last dst_slot used
        else if (iter == keymgr_dpe_pkg::DpeNumSlots) begin
          src_slot = $urandom_range(0,2);
          dst_slot ++;
        end
        `uvm_info(`gfn,
          $sformatf("Key Manager DPE Smoke Iter %0d: src_slot %d dst_slot %d",
            iter, src_slot ,dst_slot), UVM_HIGH)
        keymgr_dpe_operations(.advance_state(1), .num_gen_op($urandom_range(1,4)), .clr_output(1));
      end

      // check to make sure all key slots are valid
      for (int slot = 0; slot < keymgr_dpe_pkg::DpeNumSlots; slot++) begin
        `DV_CHECK_EQ(cfg.keymgr_dpe_vif.internal_key_slots[slot].valid, 1)
      end
  endtask : body

endclass : keymgr_dpe_smoke_vseq
