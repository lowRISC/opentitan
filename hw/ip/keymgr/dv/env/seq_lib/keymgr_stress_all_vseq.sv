// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all keymgr seqs (except below seqs) in one seq to run sequentially
// 1. csr seq, which requires scb to be disabled
// 2. keymgr_cfg_regwen_vseq as it's very timing sensitive
class keymgr_stress_all_vseq extends keymgr_base_vseq;
  `uvm_object_utils(keymgr_stress_all_vseq)

  `uvm_object_new

  // dut_init/keymgr_init is done in each sub-vseq
  // some vseq like keymgr_common_vseq should not invoke keymgr_init.
  // Let sub-vseq do dut_init/keymgr_init and don't do it in stress_all
  virtual task pre_start();
    do_dut_init = 1'b0;
    super.pre_start();
  endtask

  task body();
    string seq_names[] = {"keymgr_smoke_vseq",
                          "keymgr_common_vseq", // for intr_test
                          "keymgr_sideload_vseq",
                          "keymgr_random_vseq",
                          "keymgr_direct_to_disabled_vseq",
                          "keymgr_sw_invalid_input_vseq",
                          // TODO, add this later
                          // "keymgr_hwsw_invalid_input_vseq",
                          "keymgr_lc_disable_vseq"
                          };
    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence     seq;
      keymgr_base_vseq keymgr_vseq;
      uint             seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(keymgr_vseq, seq)

      // at the end of each vseq, design has enterred StDisabled, need to reset to recover
      // if upper seq disables do_apply_reset for this seq, then can't issue reset
      // as upper seq may drive reset
      if (do_apply_reset) keymgr_vseq.do_apply_reset = 1;
      else                keymgr_vseq.do_apply_reset = 0;

      keymgr_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(keymgr_vseq)
      if (seq_names[seq_idx] == "keymgr_common_vseq") begin
        keymgr_common_vseq common_vseq;
        `downcast(common_vseq, keymgr_vseq);
        common_vseq.common_seq_type = "intr_test";
      end

      `uvm_info(`gfn, $sformatf("Seq %s start", seq_names[seq_idx]), UVM_HIGH)
      keymgr_vseq.start(p_sequencer);

      // this is for keymgr_stress_all_with_rand_reset
      // we need to reset for each vseq, but in keymgr_stress_all_with_rand_reset, reset should be
      // issued in upper seq. So, wait forever until reset is issued and this vseq is killed by
      // upper seq
      if (!do_apply_reset) wait(0);
    end
  endtask : body

endclass
