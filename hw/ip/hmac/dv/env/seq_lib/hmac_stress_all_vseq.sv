// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all hmac seqs (except below seqs) in one seq to run sequentially
// 1. csr seq, which requires scb to be disabled
class hmac_stress_all_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_stress_all_vseq)

  `uvm_object_new

  task body();
    string seq_names[] = {"hmac_smoke_vseq",
                          "hmac_back_pressure_vseq",
                          "hmac_burst_wr_vseq",
                          "hmac_common_vseq", // for intr_test
                          "hmac_datapath_stress_vseq",
                          "hmac_long_msg_vseq",
                          "hmac_error_vseq",
                          "hmac_test_vectors_sha_vseq",
                          "hmac_test_vectors_hmac_vseq"};
    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence   seq;
      hmac_base_vseq hmac_vseq;
      uint           seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(hmac_vseq, seq)

      // dut_init (reset) can be skipped
      if (do_apply_reset) hmac_vseq.do_apply_reset = $urandom_range(0, 1);
      else hmac_vseq.do_apply_reset = 0;

      hmac_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(hmac_vseq)
      // common sequences only intr_test enabled scb
      if (seq_names[seq_idx] == "hmac_common_vseq") begin
        hmac_common_vseq common_vseq;
        `downcast(common_vseq, hmac_vseq)
        common_vseq.common_seq_type = "intr_test";
      end
      hmac_vseq.start(p_sequencer);
    end
  endtask : body

endclass
