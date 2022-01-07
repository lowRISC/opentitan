// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all edn seqs (except below seqs) in one seq to run sequentially
// 1. csr seq, which requires scb to be disabled
class edn_stress_all_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_stress_all_vseq)

  `uvm_object_new

  task body();
    string seq_names[] = {"edn_smoke_vseq",
                          "edn_common_vseq", // for intr_test
                          "edn_genbits_vseq"};

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence    seq;
      edn_base_vseq   edn_vseq;
      uint            seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(edn_vseq, seq)

      // dut_init (reset) can be skipped
      if (do_apply_reset) edn_vseq.do_apply_reset = $urandom_range(0, 1);
      else edn_vseq.do_apply_reset = 0;

      edn_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(edn_vseq)
      // common sequences only intr_test enabled scb
      if (seq_names[seq_idx] == "edn_common_vseq") begin
        edn_common_vseq   common_vseq;
        `downcast(common_vseq, edn_vseq)
        common_vseq.common_seq_type = "intr_test";
      end
      edn_vseq.start(p_sequencer);
    end
  endtask : body

endclass
