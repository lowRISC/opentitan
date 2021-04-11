// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all otp_ctrl seqs (except below seqs) in one seq to run sequentially
// Exception: - csr seq, which requires scb to be disabled.
//            - regwen_vseq, which is time sensitive and requires zero delays.
//            - otp_ctrl_macro_errs_vseq otp_ctrl_check_fail, these two sequences require to write
//              back to OTP once fatal error is triggered, thus does not handle random reset.
//            - otp_ctrl_partition_walk_vseq, this sequence assumes OTP initial value is 0.
class otp_ctrl_stress_all_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_stress_all_vseq)

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    // Drive dft_en pins to access the test_access memory, this is used for tl_error sequence in
    // stress_all_with_rand_reset test
    cfg.otp_ctrl_vif.drive_lc_dft_en(lc_ctrl_pkg::On);
    if ($urandom_range(0, 1)) cfg.otp_ctrl_vif.drive_lc_escalate_en(lc_ctrl_pkg::Off);

    // Once turn on lc_dft_en regiser, will need some time to update the state register
    // Two clock cycles for lc_async mode, one clock cycle for driving dft_en
    cfg.clk_rst_vif.wait_clks(3);
  endtask

  task body();
    string seq_names[] = {"otp_ctrl_common_vseq",
                          "otp_ctrl_dai_errs_vseq",
                          "otp_ctrl_dai_lock_vseq",
                          "otp_ctrl_smoke_vseq",
                          "otp_ctrl_test_access_vseq",
                          "otp_ctrl_background_chks_vseq",
                          // TODO: support this seq:
                          // "otp_ctrl_parallel_lc_req_vseq",
                          "otp_ctrl_parallel_lc_esc_vseq",
                          "otp_ctrl_parallel_key_req_vseq"};

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence       seq;
      otp_ctrl_base_vseq otp_ctrl_vseq;
      uint seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(otp_ctrl_vseq, seq)


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
      otp_ctrl_vseq.collect_used_addr = 0;
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
    end
  endtask : body

  virtual task read_and_check_all_csrs_after_reset();
    cfg.otp_ctrl_vif.drive_lc_escalate_en(lc_ctrl_pkg::Off);
    otp_pwr_init();
    super.read_and_check_all_csrs_after_reset();
  endtask

endclass

