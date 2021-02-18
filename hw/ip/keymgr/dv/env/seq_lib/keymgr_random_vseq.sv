// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Randomize sw control content: version, rom_ext_desc, salt, binding.
class keymgr_random_vseq extends keymgr_sideload_vseq;
  `uvm_object_utils(keymgr_random_vseq)
  `uvm_object_new

  rand uint num_invalid_hw_input;

  // don't test invalid HW input in this test
  constraint num_invalid_hw_input_c {
    num_invalid_hw_input == 0;
  }

  task write_random_sw_content();
    uvm_reg         csr_update_q[$];

    csr_random_n_add_to_q(ral.sw_binding_regwen, csr_update_q);
    csr_random_n_add_to_q(ral.sw_binding_0, csr_update_q);
    csr_random_n_add_to_q(ral.sw_binding_1, csr_update_q);
    csr_random_n_add_to_q(ral.sw_binding_2, csr_update_q);
    csr_random_n_add_to_q(ral.sw_binding_3, csr_update_q);
    csr_random_n_add_to_q(ral.salt_0, csr_update_q);
    csr_random_n_add_to_q(ral.salt_1, csr_update_q);
    csr_random_n_add_to_q(ral.salt_2, csr_update_q);
    csr_random_n_add_to_q(ral.salt_3, csr_update_q);

    csr_random_n_add_to_q(ral.max_creator_key_ver, csr_update_q);
    csr_random_n_add_to_q(ral.max_owner_int_key_ver, csr_update_q);
    csr_random_n_add_to_q(ral.max_owner_key_ver, csr_update_q);

    csr_random_n_add_to_q(ral.max_creator_key_ver_regwen, csr_update_q);
    csr_random_n_add_to_q(ral.max_owner_int_key_ver_regwen, csr_update_q);
    csr_random_n_add_to_q(ral.max_owner_key_ver_regwen, csr_update_q);
    csr_random_n_add_to_q(ral.key_version, csr_update_q);

    csr_update_q.shuffle();
    foreach (csr_update_q[i]) csr_update(csr_update_q[i]);
  endtask : write_random_sw_content

  task csr_random_n_add_to_q(uvm_reg csr, ref uvm_reg csr_q[$]);
    `DV_CHECK_RANDOMIZE_FATAL(csr)
    csr_q.push_back(csr);
  endtask

  virtual task keymgr_operations(bit advance_state = $urandom_range(0, 1),
                                 int num_gen_op    = $urandom_range(1, 4),
                                 bit clr_output    = $urandom_range(0, 1),
                                 bit wait_done     = 1);
    if ($urandom_range(0, 1)) begin
      `uvm_info(`gfn, "Write random SW content", UVM_MEDIUM)
      write_random_sw_content();
    end
    if ($urandom_range(0, 1)) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_invalid_hw_input)
      `uvm_info(`gfn, $sformatf("Drive random HW data with %0d invalid inputs",
                                num_invalid_hw_input), UVM_MEDIUM)
      cfg.keymgr_vif.drive_random_hw_input_data(num_invalid_hw_input);
    end
    super.keymgr_operations(advance_state, num_gen_op, clr_output, wait_done);
  endtask : keymgr_operations

  // override body to add more randomization
  task body();
    keymgr_pkg::keymgr_working_state_e state;
    `uvm_info(`gfn, "Key manager seq start", UVM_HIGH)
    // Advance from StReset to last state StDisabled and advance one extra time,
    // then it should stay at StDisabled
    // In each state check SW/HW output
    repeat (state.num() + 1) begin
      keymgr_operations(.advance_state(1),
                        .num_gen_op($urandom_range(0, 5)),
                        .clr_output($urandom_range(0, 1)));
    end

  endtask : body

endclass : keymgr_random_vseq
