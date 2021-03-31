// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all otp_ctrl seqs (except below seqs) in one seq to run sequentially
// Exception: - csr seq, which requires scb to be disabled
//            - regwen_vseq, which is time sensitive and requires zero delays
class otp_ctrl_stress_all_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_stress_all_vseq)

  `uvm_object_new

  task body();
    // TODO: support more sequences
    string seq_names[] = {//"otp_ctrl_common_vseq",
                          "otp_ctrl_dai_errs_vseq",
                          "otp_ctrl_dai_lock_vseq",
                          "otp_ctrl_smoke_vseq"};

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence       seq;
      otp_ctrl_base_vseq otp_ctrl_vseq;
      uint seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(otp_ctrl_vseq, seq)

      // if upper seq disables do_apply_reset for this seq, then can't issue reset
      // as upper seq may drive reset
      if (do_apply_reset) begin
        otp_ctrl_vseq.do_apply_reset = $urandom_range(0, 1);
      end else begin
        otp_ctrl_vseq.do_apply_reset = 0;
      end

      otp_ctrl_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(otp_ctrl_vseq)
      if (seq_names[seq_idx] == "otp_ctrl_common_vseq") begin
        otp_ctrl_common_vseq common_vseq;
        `downcast(common_vseq, otp_ctrl_vseq);
        common_vseq.common_seq_type = "intr_test";
      end

      // Pass local variables to next sequence due to randomly issued reset.
      otp_ctrl_vseq.collect_used_addr = 0;
      otp_ctrl_vseq.is_valid_dai_op = 0;
      otp_ctrl_vseq.lc_prog_blocking = this.lc_prog_blocking;
      otp_ctrl_vseq.digest_calculated = this.digest_calculated;
      otp_ctrl_vseq.start(p_sequencer);

      this.lc_prog_blocking = otp_ctrl_vseq.lc_prog_blocking;
      this.digest_calculated = otp_ctrl_vseq.digest_calculated;
    end
  endtask : body

  virtual task post_start();
    apply_reset();

    // delay to avoid race condition when sending item and checking no item after reset occur
    // at the same time
    #1ps;
    super.post_start();
  endtask

endclass

