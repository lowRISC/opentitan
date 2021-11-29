// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Otp_ctrl_parallel_lc_vseq is developed to generate rand lc_otp req, which runs parallel with
// normal DAI access sequences.
class otp_ctrl_parallel_lc_req_vseq extends otp_ctrl_parallel_base_vseq;
  `uvm_object_utils(otp_ctrl_parallel_lc_req_vseq)

  `uvm_object_new

  // Disable the default LC program request from otp_ctrl_smoke_vseq.
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
            // Because LC program request is issued in parallel with DAI access, we disable
            // interrupt check in this task.
            // We only check interrupts when DAI access and LC program request are done.
            req_lc_transition(0, lc_prog_blocking);
          end
        end
      end join
    end
  endtask

  virtual task post_start();
    expect_fatal_alerts = 1;
    super.post_start();
  endtask

endclass
