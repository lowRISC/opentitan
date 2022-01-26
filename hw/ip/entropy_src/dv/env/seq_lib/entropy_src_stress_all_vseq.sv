// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all entropy_src seqs (except below seqs) in one seq to run sequentially
// 1. csr seq, which requires scb to be disabled
class entropy_src_stress_all_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_stress_all_vseq)

  `uvm_object_new

  task body();
    string seq_names[] = {"entropy_src_smoke_vseq",
                          "entropy_src_common_vseq", // for intr_test
                          "entropy_src_rng_vseq"};

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence            seq;
      entropy_src_base_vseq   entropy_src_vseq;
      uint                    seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(entropy_src_vseq, seq)

      // dut_init (reset) can be skipped
      if (do_apply_reset) entropy_src_vseq.do_apply_reset = $urandom_range(0, 1);
      else entropy_src_vseq.do_apply_reset = 0;

      entropy_src_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(entropy_src_vseq)
      // common sequences only intr_test enabled scb
      if (seq_names[seq_idx] == "entropy_src_common_vseq") begin
        entropy_src_common_vseq   common_vseq;
        `downcast(common_vseq, entropy_src_vseq)
        common_vseq.common_seq_type = "intr_test";
      end
      entropy_src_vseq.start(p_sequencer);
    end
  endtask : body

endclass
