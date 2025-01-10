// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Combine all otp_ctrl seqs (except below seqs) in one seq to run sequentially.
// Exception: - csr seq: requires scb to be disabled
//            - regwen_vseq and parallel_lc_vseq: time sensitive thus require zero_delays
//            - macro_errs_vseq and check_fail_vseq: require to write back to OTP once fatal
//              error is triggered, thus does not handle random reset
//            - partition_walk_vseq: assume OTP initial value is 0
//            - init_fail: requires resets in the middle of the sequence
class otp_ctrl_stress_all_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_stress_all_vseq)

  string seq_names[];

  `uvm_object_new

  virtual function void assign_seq_names();
    seq_names = {"otp_ctrl_common_vseq",
                 "otp_ctrl_dai_lock_vseq",
                 "otp_ctrl_smoke_vseq",
                 "otp_ctrl_test_access_vseq",
                 "otp_ctrl_background_chks_vseq",
                 "otp_ctrl_parallel_lc_esc_vseq",
                 "otp_ctrl_parallel_lc_req_vseq",
                 "otp_ctrl_parallel_key_req_vseq",
                 "otp_ctrl_dai_errs_vseq",
                 "otp_ctrl_low_freq_read_vseq"};
  endfunction

  task body();
    assign_seq_names();

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence       seq;
      otp_ctrl_base_vseq otp_ctrl_vseq;
      uint seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(otp_ctrl_vseq, seq)
      `uvm_info(`gfn, $sformatf("Starting sequence %s in stress_all", otp_ctrl_vseq.get_name()),
                UVM_MEDIUM)

      // At the end of each vseq, design might enter terminal Error State, need to reset to
      // recover. If upper seq disables do_apply_reset for this seq, then can't issue reset
      // as upper seq may drive reset.
      if (do_apply_reset) otp_ctrl_vseq.do_apply_reset = 1;
      else                otp_ctrl_vseq.do_apply_reset = 0;

      otp_ctrl_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(otp_ctrl_vseq)
      if (seq_names[seq_idx] == "otp_ctrl_common_vseq") begin
        otp_ctrl_common_vseq common_vseq;
        `downcast(common_vseq, otp_ctrl_vseq);
        common_vseq.common_seq_type = "intr_test";
      end

      // Pass local variables to next sequence due to randomly issued reset.
      otp_ctrl_vseq.is_valid_dai_op = 0;
      otp_ctrl_vseq.lc_prog_blocking = this.lc_prog_blocking;
      otp_ctrl_vseq.digest_calculated = this.digest_calculated;
      otp_ctrl_vseq.start(p_sequencer);

      this.lc_prog_blocking = otp_ctrl_vseq.lc_prog_blocking;
      this.digest_calculated = otp_ctrl_vseq.digest_calculated;

      // This is for otp_ctrl_stress_all_with_rand_reset.
      // We need to reset for each vseq, but in otp_ctrl_stress_all_with_rand_reset, reset should be
      // issued in upper seq. So, wait forever until reset is issued and this vseq is killed by
      // upper seq.
      if (!do_apply_reset) wait(0);

      // This is only valid for stress_all sequence.
      // For stress_all_with_rand_reset sequence, the logic will be gated at previous line and will
      // enable scb again at `apply_resets_concurrently` task.
      cfg.en_scb = 1;
    end
  endtask : body

endclass
