// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Otp_ctrl_parallel_lc_vseq is developed to generate rand lc_otp req, which runs parallel with
// normal DAI access sequences.
class otp_ctrl_parallel_lc_req_vseq extends otp_ctrl_parallel_base_vseq;
  `uvm_object_utils(otp_ctrl_parallel_lc_req_vseq)

  `uvm_object_new

  // disable checks in case lc_program and check triggered at the same time
  constraint regwens_c {
    check_regwen_val dist {0 :/ 1, 1 :/ 9};
    check_trigger_regwen_val == 0;
  }

  constraint lc_trans_c {
    do_lc_trans == 0;
  }

  virtual task run_parallel_seq(ref bit base_vseq_done);
    forever begin
      if (base_vseq_done) return;

      fork begin
        if ($urandom_range(0, 1)) begin
          wait_clk_or_reset($urandom_range(0, 500));
          if (!base_vseq_done && !cfg.under_reset) begin
            // TODO: current if reset is issued during OTP write, scb cannot predict if how many
            // OTP cells have been written.
            do_reset_in_seq = 0;
            req_lc_transition(0, lc_prog_blocking);
            do_reset_in_seq = 1;
          end
        end
      end join
    end
  endtask

  virtual task post_start();
    // Use reset to clear lc interrupt error
    if (do_apply_reset) begin
      dut_init();
    end else wait(0); // wait until upper seq resets and kills this seq

    // delay to avoid race condition when sending item and checking no item after reset occur
    // at the same time
    #1ps;
    super.post_start();
  endtask

endclass
