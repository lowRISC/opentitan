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
    // TODO: support enable req_key while lc_escalate_en is set.
    do_req_keys == 0;
  }

  // disable err_code check because cannot accurately predict when LC error is detected
  constraint no_err_code_c {
    check_err_code == 0;
  }

  virtual task run_parallel_seq(ref bit base_vseq_done);
    forever
      begin
        if (base_vseq_done) return;

        fork
          begin
            if ($urandom_range(0, 1)) begin
              wait_clk_or_reset($urandom_range(0, 500));
              if (!base_vseq_done && !cfg.under_reset) req_lc_transition();
            end
          end
          begin
            // req lc token request
            if ($urandom_range(0, 1)) begin
              wait_clk_or_reset($urandom_range(0, 500));
              if (!base_vseq_done && !cfg.under_reset) req_lc_token();
            end
          end
          begin
            // req lc token request
            if ($urandom_range(0, 1)) begin
              wait_clk_or_reset($urandom_range(0, 500));
              if (!base_vseq_done && !cfg.under_reset) begin
                // TODO: random drive any values instead of just on and off
                cfg.otp_ctrl_vif.drive_lc_escalate_en(lc_ctrl_pkg::On);
                // TODO: check with designer if we can take away this asssertoff
                $assertoff(0, "tb.dut.u_otp_arb");
                // Turn off reset because if issuing lc_escalation_en during otp program, scb cannot
                // predict if the OTP memory is programmed or not.
                do_reset_in_seq = 0;
              end
            end
          end
        join
      end
  endtask

  // Use reset to clear lc interrupt error
  virtual task post_start();
    if (do_apply_reset) begin
      apply_reset();
      cfg.otp_ctrl_vif.drive_lc_escalate_en(lc_ctrl_pkg::Off);
    end else wait(0); // wait until upper seq resets and kills this seq

    // delay to avoid race condition when sending item and checking no item after reset occur
    // at the same time
    #1ps;
    super.post_start();
  endtask

endclass
