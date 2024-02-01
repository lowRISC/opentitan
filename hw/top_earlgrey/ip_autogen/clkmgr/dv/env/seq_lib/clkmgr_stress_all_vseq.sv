// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all clkmgr seqs (except below seqs) in one seq to run sequentially
// 1. csr seq, which requires scb to be disabled
class clkmgr_stress_all_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_stress_all_vseq)

  `uvm_object_new

  task body();
    string seq_names[] = {
      "clkmgr_extclk_vseq",
      "clkmgr_frequency_timeout_vseq",
      "clkmgr_frequency_vseq",
      "clkmgr_peri_vseq",
      "clkmgr_smoke_vseq",
      "clkmgr_trans_vseq"
    };
    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence     seq;
      clkmgr_base_vseq clkmgr_vseq;
      uint             seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(clkmgr_vseq, seq)

      // if upper seq disables do_apply_reset for this seq, then can't issue reset
      // as upper seq may drive reset
      if (do_apply_reset) clkmgr_vseq.do_apply_reset = $urandom_range(0, 1);
      else clkmgr_vseq.do_apply_reset = 0;
      clkmgr_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(clkmgr_vseq)
      `uvm_info(`gfn, $sformatf("seq_idx = %0d, sequence is %0s", seq_idx, clkmgr_vseq.get_name()),
                UVM_MEDIUM)

      clkmgr_vseq.start(p_sequencer);
      `uvm_info(`gfn, $sformatf(
                "End of sequence %0s with seq_idx = %0d", clkmgr_vseq.get_name(), seq_idx),
                UVM_MEDIUM)
    end
  endtask : body
endclass
