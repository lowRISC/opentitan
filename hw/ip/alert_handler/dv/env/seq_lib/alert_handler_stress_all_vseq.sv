// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all alert_handler seqs (except below seqs) in one seq to run sequentially
// 1. csr seq, which requires scb to be disabled
class alert_handler_stress_all_vseq extends alert_handler_base_vseq;
  `uvm_object_utils(alert_handler_stress_all_vseq)

  `uvm_object_new

  task body();
    bit entropy_test_flag; // this flag ensures entropy test only runs once due to its long runtime
    string seq_names[] = {"alert_handler_smoke_vseq",
                          "alert_handler_random_alerts_vseq",
                          "alert_handler_random_classes_vseq",
                          "alert_handler_esc_intr_timeout_vseq",
                          "alert_handler_esc_alert_accum_vseq",
                          "alert_handler_sig_int_fail_vseq",
                          "alert_handler_entropy_vseq"};
    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence            seq;
      alert_handler_base_vseq alert_vseq;
      uint seq_idx = entropy_test_flag ? $urandom_range(0, seq_names.size - 2) :
                                         $urandom_range(0, seq_names.size - 1);
      if (seq_names[seq_idx] == "alert_handler_entropy_vseq") entropy_test_flag = 1;

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(alert_vseq, seq)

      // if upper seq disables do_apply_reset for this seq, then can't issue reset
      // as upper seq may drive reset
      if (do_apply_reset) begin
        alert_vseq.do_apply_reset = $urandom_range(0, 1);
        // config_locked will be set unless reset is issued
        alert_vseq.config_locked = alert_vseq.do_apply_reset ? 0 : config_locked;
      end else begin
        alert_vseq.do_apply_reset = 0;
        alert_vseq.config_locked = config_locked;
      end

      alert_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(alert_vseq)
      if (seq_names[seq_idx] == "alert_common_vseq") begin
        alert_handler_common_vseq common_vseq;
        `downcast(common_vseq, alert_vseq);
        common_vseq.common_seq_type = "intr_test";
      end

      alert_vseq.start(p_sequencer);
      config_locked = alert_vseq.config_locked;
    end
  endtask : body

endclass

