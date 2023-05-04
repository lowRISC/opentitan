// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_stress_all_vseq extends aon_timer_base_vseq;
  `uvm_object_utils(aon_timer_stress_all_vseq)

  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[15:20]};
  }

  task body();
    string seq_names[] = {"aon_timer_smoke_vseq",
                          "aon_timer_prescaler_vseq",
                          "aon_timer_jump_vseq",
                          "aon_timer_common_vseq"};

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence        seq;
      aon_timer_base_vseq aon_timer_vseq;
      uint                seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(aon_timer_vseq, seq)

      // if upper seq disables do_apply_reset for this seq, then can't issue reset
      // as upper seq may drive reset
      if (do_apply_reset) aon_timer_vseq.do_apply_reset = $urandom_range(0, 1);
      else                aon_timer_vseq.do_apply_reset = 0;

      aon_timer_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(aon_timer_vseq)
      if (seq_names[seq_idx] == "aon_timer_common_vseq") begin
        aon_timer_common_vseq common_vseq;
        `downcast(common_vseq, aon_timer_vseq);
        common_vseq.common_seq_type = "intr_test";
      end

      aon_timer_vseq.start(p_sequencer);
    end
  endtask : body

endclass
