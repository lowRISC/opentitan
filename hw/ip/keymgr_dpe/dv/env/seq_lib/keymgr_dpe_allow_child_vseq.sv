// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_dpe_allow_child_vseq extends keymgr_dpe_base_vseq;
  `uvm_object_utils(keymgr_dpe_allow_child_vseq)
  `uvm_object_new

  // holds slots that are used so that we don't inadvertently
  // target the same key slot for dst slot of an advance
  keymgr_dpe_pkg::keymgr_dpe_slot_idx_e used_slot[$];
  // holds the initial key slot used to be advanced with at end of test
  keymgr_dpe_pkg::keymgr_dpe_slot_idx_e valid_slot;

  constraint gen_operation_c {
    gen_operation inside {
      keymgr_dpe_pkg::OpDpeGenHwOut,
      keymgr_dpe_pkg::OpDpeGenSwOut
    };
  }

  constraint slot_vals_c {
    src_slot inside {[0:keymgr_dpe_pkg::DpeNumSlots-1]};
    dst_slot inside {[0:keymgr_dpe_pkg::DpeNumSlots-1]};
  }

  task body();
    // This sequence latches the OTP key then advances with a key policy with allow child == 0
    // there are attempts to advance for the key slot with allow child == 0.
    // and these are expected to fail. The checks will be done via the scb
    `uvm_info(`gfn, "Key Manager DPE Allow Child start", UVM_HIGH)

    // 1. latch the OTP key
    // - by default the key policy at the dst slot here will have allow_child == 1
    //   and retain_parent == 0
    `uvm_info(`gfn,
      $sformatf("Key Manager DPE Allow Child latch OTP key: src_slot %d dst_slot %d policy %p",
        src_slot, dst_slot, policy), UVM_HIGH)
        keymgr_dpe_operations(.advance_state(1), .num_gen_op($urandom_range(5,10)), .clr_output(1));
    used_slot.push_back(dst_slot);
    valid_slot = dst_slot;
    otp_latched = 1'b1;

    // 2. Adance from the OTP key.
    // - dst slot would be the same as src slot because of retain parent == 0
    //   of the OTP policy which is attached to the src slot
    src_slot = dst_slot;
    // - randomize a new key policy to be attached to the newly advanced key at the dst slot
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(policy,
                                          policy.retain_parent == 1;
                                          policy.allow_child == 1;)
    `uvm_info(`gfn,
    $sformatf({"Key Manager DPE Allow Child first advance post latch OTP key:",
               "src_slot %d dst_slot %d policy %p"},
                src_slot, dst_slot, policy), UVM_HIGH)
    keymgr_dpe_operations(.advance_state(1), .num_gen_op($urandom_range(5,10)), .clr_output(1));

    // 3. Advance again to create the key with allow_child == 0 key policy
    // - in this case use a different dst slot from the src slot because
    //   the src slot's policy has retain_parent == 1
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(dst_slot, dst_slot != src_slot;)
    // - randomize a new key policy to be attached to the newly advanced key with allow child == 0
    //   and that will be attached to the dst slot
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(policy,
                                          policy.retain_parent == 1;
                                          policy.allow_child == 0;)
    `uvm_info(`gfn,
    $sformatf({"Key Manager DPE Allow Child second advance post latch OTP key:",
              "src_slot %d dst_slot %d policy %p"},
               src_slot, dst_slot, policy), UVM_HIGH)
    keymgr_dpe_operations(.advance_state(1), .num_gen_op($urandom_range(5,10)), .clr_output(1));
    used_slot.push_back(dst_slot);

    // 4. Advances that should fail.
    // - using the previous dst key slot as the src slot
    //   that should have allow_child == 0 as it's attached key policy. this advancement
    //   should fail because of that
    // - randomize the dst_slot to not equal the src_slot, this is because the src_slot
    // has a policy of retain_parent == 1.
    src_slot = dst_slot;
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(dst_slot,
                                          dst_slot != src_slot;
                                          foreach (used_slot[idx]) used_slot[idx] != dst_slot;)
    // - attempt to advance multiple times with a random policy each time. These should all fail
    //   due to allow_child of the src_slot being 0
    repeat(10) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(policy)
      `uvm_info(`gfn,
        $sformatf({"Key Manager DPE Allow Child advance on slot with allow child == 0:",
                   "src_slot %d dst_slot %d policy %p"},
                    src_slot, dst_slot, policy), UVM_HIGH)
      keymgr_dpe_operations(.advance_state(1), .num_gen_op($urandom_range(5,10)), .clr_output(1));
    end

    // 5. Advance that should succeed.
    // - This should expose any issues with recovering from
    //   an allow_child error
    // - randomize the src slot to be the initial src slot that the OTP was latched too
    //   this slot will have allow child == 1 and retain parent == 1, so the dst slot should not be
    //   the same as the src slot
    src_slot = valid_slot;
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(dst_slot,
                                          dst_slot != src_slot;
                                          foreach (used_slot[idx]) used_slot[idx] != dst_slot;)
    `uvm_info(`gfn,
      $sformatf({"Key Manager DPE Allow Child final advance on slot with allow child == 1:",
                 "src_slot %d dst_slot %d policy %p"},
                  src_slot, dst_slot, policy), UVM_HIGH)
    keymgr_dpe_operations(.advance_state(1), .num_gen_op($urandom_range(5,10)), .clr_output(1));
  endtask : body

endclass : keymgr_dpe_allow_child_vseq
