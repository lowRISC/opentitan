// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs other sequences one after the other and randomly injects resets between
// sequences.

class aes_stress_all_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_stress_all_vseq)
  `uvm_object_new

  // The sequences that we'll run back-to-back.
  string vseq_names[$] = {
    "aes_stress_vseq",
    "aes_alert_reset_vseq",
    "aes_reseed_vseq"
  };

  task body();
    `uvm_info(`gfn, $sformatf("Running %0d sub-sequences", num_trans), UVM_LOW)
    for (int i = 0; i < num_trans; i++) begin
      uvm_sequence   seq;
      aes_base_vseq  aes_vseq;
      uint           seq_idx = $urandom_range(0, vseq_names.size() - 1);
      string         cur_vseq_name = vseq_names[seq_idx];

      seq = create_seq_by_name(cur_vseq_name);
      `downcast(aes_vseq, seq)

      aes_vseq.do_apply_reset = (do_apply_reset) ? $urandom_range(0, 1) : 0;
      aes_vseq.set_sequencer(p_sequencer);
      `uvm_info(`gfn, $sformatf("iteration[%0d]: starting %0s, resetting %0d",
          i, cur_vseq_name, aes_vseq.do_apply_reset), UVM_LOW)
      aes_vseq.start(p_sequencer);
      `uvm_info(`gfn, $sformatf("iteration[%0d]: ending %0s", i, cur_vseq_name), UVM_LOW)
    end
  endtask

endclass
