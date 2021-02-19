// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all rv_timer seqs (except below seqs) in one seq to run sequentially
// 1. csr seq, which requires scb to be disabled
// 2. rv_timer_cfg_update_on_fly, which requires zero_delays as it's very timing sensitive
class rv_timer_stress_all_vseq extends rv_timer_base_vseq;
  `uvm_object_utils(rv_timer_stress_all_vseq)

  `uvm_object_new

  // avoid simulation running for too long
  constraint num_trans_c {
    num_trans inside {[1:10]};
  }


  task body();
    string seq_names[] = {"rv_timer_random_vseq",
                          "rv_timer_disabled_vseq",
                          "rv_timer_common_vseq"}; // for intr_test
    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence       seq;
      rv_timer_base_vseq rv_timer_vseq;
      uint               seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(rv_timer_vseq, seq)

      // dut_init (reset) can be skipped
      if (do_apply_reset) rv_timer_vseq.do_apply_reset = $urandom_range(0, 1);
      else rv_timer_vseq.do_apply_reset = 0;

      rv_timer_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(rv_timer_vseq)
      if (seq_names[seq_idx] == "rv_timer_common_vseq") begin
        rv_timer_common_vseq common_vseq;
        `downcast(common_vseq, rv_timer_vseq);
        common_vseq.common_seq_type = "intr_test";
      end

      rv_timer_vseq.start(p_sequencer);
    end
  endtask : body

endclass
