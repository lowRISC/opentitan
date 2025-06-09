// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_stress_all_vseq extends ac_range_check_base_vseq;
  `uvm_object_utils(ac_range_check_stress_all_vseq)

  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[3:6]};
  }

  task body();
    // ac-range_check_lock_range is removed since it corrupts the stress test. If lock_range test
    // is executed no other test that follow the lock test will pass as the range indexes will be
    // locked and can only be released via a HARD reset.
    string seq_names[] = {
      "ac_range_check_smoke_vseq",
      "ac_range_check_smoke_racl_vseq",
      "ac_range_check_bypass_vseq"
    };

    // Reset testing in sequences is flaky. At this time make sure all reset capability is disabled
    this.do_apply_reset = 0;

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence             seq;
      ac_range_check_base_vseq ac_range_check_vseq;

      uint seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(ac_range_check_vseq, seq)

      ac_range_check_vseq.do_apply_reset = this.do_apply_reset;

      ac_range_check_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(ac_range_check_vseq)

      `uvm_info(`gfn, $sformatf("starting stress_all sub-sequence %s", seq_names[seq_idx]), UVM_LOW)
      ac_range_check_vseq.start(p_sequencer);
    end
  endtask : body

endclass
