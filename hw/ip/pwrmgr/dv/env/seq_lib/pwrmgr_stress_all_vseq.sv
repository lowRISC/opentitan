// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all pwrmgr seqs (except below seqs) in one seq to run sequentially
// 1. csr seq, which requires scb to be disabled
class pwrmgr_stress_all_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_stress_all_vseq)

  `uvm_object_new

  task body();
    string seq_names[] = {
      "pwrmgr_aborted_low_power_vseq",
      "pwrmgr_lowpower_wakeup_race_vseq",
      "pwrmgr_reset_vseq",
      "pwrmgr_smoke_vseq",
      "pwrmgr_wakeup_reset_vseq",
      "pwrmgr_wakeup_vseq"
    };

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence     seq;
      pwrmgr_base_vseq pwrmgr_vseq;
      uint             seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(pwrmgr_vseq, seq)

      pwrmgr_vseq.do_apply_reset = 1;
      pwrmgr_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(pwrmgr_vseq)
      `uvm_info(`gfn, $sformatf("seq_idx = %0d, sequence is %0s", seq_idx, pwrmgr_vseq.get_name()),
                UVM_MEDIUM)

      pwrmgr_vseq.start(p_sequencer);
      `uvm_info(`gfn, $sformatf(
                "End of sequence %0s with seq_idx = %0d", pwrmgr_vseq.get_name(), seq_idx),
                UVM_MEDIUM)
    end
  endtask : body
endclass
