// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs other sequences one after the other. This *always* re-loads binaries, which
// is different from otbn_multi_vseq where we are cleverer about reloading things.

class otbn_stress_all_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_stress_all_vseq)

  `uvm_object_new

  // The sequences that we'll run back-to-back
  string vseq_names[$] = {
    "otbn_dmem_err_vseq",
    "otbn_imem_err_vseq",
    "otbn_single_vseq"
  };

  task body();
    `uvm_info(`gfn, $sformatf("Running %0d sub-sequences", num_trans), UVM_LOW)
    for (int i = 0; i < num_trans; i++) begin
      uvm_sequence   seq;
      otbn_base_vseq otbn_vseq;
      uint           seq_idx = $urandom_range(0, vseq_names.size() - 1);
      string         cur_vseq_name = vseq_names[seq_idx];

      seq = create_seq_by_name(cur_vseq_name);
      `downcast(otbn_vseq, seq)

      // Only force a reset at the start of the sequence if OTBN is currently locked (in which case,
      // we wouldn't be able to do anything)
      otbn_vseq.do_apply_reset = (cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked);
      otbn_vseq.set_sequencer(p_sequencer);
      otbn_vseq.start(p_sequencer);
    end
  endtask

endclass
