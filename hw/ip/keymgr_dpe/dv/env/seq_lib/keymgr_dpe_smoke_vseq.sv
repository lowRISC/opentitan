// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_dpe_smoke_vseq extends keymgr_dpe_base_vseq;
  `uvm_object_utils(keymgr_dpe_smoke_vseq)
  `uvm_object_new

  constraint gen_operation_c {
    gen_operation inside {
      keymgr_dpe_pkg::OpDpeGenHwOut,
      keymgr_dpe_pkg::OpDpeGenSwOut
    };
  }

  // retain parent is 1 becuse we want to test
  // filling and emptying key slots
  constraint set_policy_c {
    policy.allow_child == 1;
    policy.exportable == 0;
    soft policy.retain_parent == 1;
  }

  // for initial latch of OTP key src slot does not matter
  // it can be completely random
  constraint initial_slot_vals_c {
    soft src_slot inside {[0:keymgr_dpe_pkg::DpeNumSlots-1]};
    (!otp_latched) -> {soft dst_slot == 0;}
  }

  task body();
    // This test does the following:
    // 1. While in reset state does a keymgr_dpe disable operation.
    //    - also does a random amount of advances and generations
    // 2. Fill key slots
    //    - latches OTP key and fills all key slots
    //    - each time doing a random amount of generations
    // 3. Erase all key slots aside from key_slot 0.
    //    - each time doing random operations with the erased slot
    //      as the src_slot
    // 4. Re-fill the erased key slots with advanced operations
    //    - also does a retain parent == 0 for the final advance
    // 5. With filled key_slots do random advance, and generate operations
    // 6. Disable keymgr_dpe and perform random advance and generations

    // Checks are done via the scoreboard, but this test does have some additional checks
    // in terms of valid bit for key slots for checking key slots are filled and empty
    `uvm_info(`gfn, "Key Manager DPE Smoke Start", UVM_HIGH)

    // 1.
    keymgr_dpe_disable();

    // 2.
    for (int iter = 0; iter<keymgr_dpe_pkg::DpeNumSlots+1; iter++) begin
      // retain_parent == 0, for the latched OTP
      // so src_slot must == dst_slot
      if (iter == 1) begin
        otp_latched = 1'b1;
        src_slot = dst_slot;
      // retain_parent == 1, for further advances calls
      // so src_slot must != dst_slot
      end else if (iter > 1 & iter < keymgr_dpe_pkg::DpeNumSlots)  begin
        src_slot = dst_slot;
        dst_slot ++;
      end
      // Boot stages 0-3 are used for previous key slots. In the final key slot
      // src_slot must differ from last iteration's dst slot. As all 4 boot stages
      // as defined by DpeNumBootStages are exhausted.
      else if (iter == keymgr_dpe_pkg::DpeNumSlots) begin
        src_slot = $urandom_range(0,(keymgr_dpe_pkg::DpeNumSlots-1)-2);
        dst_slot ++;
      end
      `uvm_info(`gfn,
        $sformatf("Key Manager DPE Smoke Iter %0d: src_slot %d dst_slot %d",
          iter, src_slot ,dst_slot), UVM_HIGH)
      keymgr_dpe_operations(.advance_state(1), .num_gen_op($urandom_range(5,10)), .clr_output(1));
    end

    // Check to make sure all key slots are valid after the advance operations
    // this is checked via the valid bit being set in the key slot
    for (int slot = 0; slot < keymgr_dpe_pkg::DpeNumSlots; slot++) begin
      `DV_CHECK_EQ(cfg.keymgr_dpe_vif.internal_key_slots[slot].valid, 1)
    end

    // 3.
    // Erase all key slots except for key slot 0. The reason is that in-order to
    // be able to re-fill the emptied key slots there needs to be at least one
    // key slot that is still valid. The reason for picking slot 0 is that it should
    // only have boot_stage 1, which gives us enough boot_stages to advance and fill
    // key_slots 1-3 again.
    for (int iter = 1; iter<keymgr_dpe_pkg::DpeNumSlots; iter++) begin
      dst_slot = iter;
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(src_slot)
      keymgr_dpe_erase(.num_adv_op(4));
    end

    // To verify the erase operation succeeded, check that the valid bits
    // of the erased key slots are not de-asserted.
    for (int slot = 1; slot < keymgr_dpe_pkg::DpeNumSlots; slot++) begin
      `DV_CHECK_EQ(cfg.keymgr_dpe_vif.internal_key_slots[slot].valid, 0)
    end

    // An additional check to make sure slot 0 is still valid after erase operations
    // as this was the only slot not erased
    `DV_CHECK_EQ(cfg.keymgr_dpe_vif.internal_key_slots[0].valid, 1)

    // 4.
    // To re-fill the key_slots set src_slot to 0 the un-erased slot
    // set dst_slot to 1, to begin filling slot 1-3 again
    src_slot = 0;
    dst_slot = 1;
    for (int iter = 0; iter<keymgr_dpe_pkg::DpeNumSlots; iter++) begin
      // The boot_stage for key_slot 2 is expected to be 3.
      // This means we can not use it to derive key_slot 3.
      // We have to use either key_slot 0 or 1. So on the final iteration
      // randomize to use either key_slot 0 or 1
      if (iter == keymgr_dpe_pkg::DpeNumSlots-2) begin
        src_slot = $urandom_range(0, 1);
        // Set retain_parent to 0. So that an additional advance can be done with the same src and dst slot
        policy.retain_parent = 0;
      end
      if (iter == keymgr_dpe_pkg::DpeNumSlots-1) begin
        src_slot = 3;
        dst_slot = 3;
      end
      keymgr_dpe_operations(.advance_state(1), .num_gen_op($urandom_range(5,10)), .clr_output(1));
      src_slot++;
      dst_slot++;
    end

    // Check to make sure all key slots are valid after the advance operations
    // this is checked via the valid bit being set in the key slot
    for (int slot = 1; slot < keymgr_dpe_pkg::DpeNumSlots; slot++) begin
      `DV_CHECK_EQ(cfg.keymgr_dpe_vif.internal_key_slots[slot].valid, 1)
    end

    // 5.
    // Do a random amount of additional advances and generates with full key slots
    // this will stress errors conditions like boot_stage, retain_parent, and key_version.
    // some will fail some may succeed, the scoreboard is responsible for doing checks on the fly
    repeat($urandom_range(5, 10)) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dst_slot)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(src_slot)
      `uvm_info(`gfn,
      $sformatf(
        {"Random Key Manager DPE Smoke randomize advance and operations:",
        "src_slot %d dst_slot %d"},
        src_slot ,dst_slot), UVM_HIGH)
      keymgr_dpe_operations(.advance_state(1), .num_gen_op($urandom_range(5,10)), .clr_output(1));
    end

    // 6.
    // Disable the key_manager and perform additional operations. Again these are expected to fail
    // and the scoreboard is responsible for checking these conditions
    keymgr_dpe_disable();
  endtask : body

endclass : keymgr_dpe_smoke_vseq
