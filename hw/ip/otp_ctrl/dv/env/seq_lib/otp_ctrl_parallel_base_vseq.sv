// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is a base sequence that serves as a template for the scenarios below:
// Two sequences run in parallel:
// 1. One sequence is otp_ctrl's DAI interface access sequence with errors
// 2. Another sequence is an empty task that needs to be override, this could be: key_request
//    sequences or lc_request sequences.

class otp_ctrl_parallel_base_vseq extends otp_ctrl_dai_errs_vseq;
  `uvm_object_utils(otp_ctrl_parallel_base_vseq)

  `uvm_object_new

  constraint num_iterations_c {
    num_trans  inside {[1:5]};
    num_dai_op inside {[1:500]};
  }

  virtual task body();
    bit base_vseq_done;

    fork
      begin
        run_parallel_seq(base_vseq_done);
      end
      begin
        super.body();
        base_vseq_done = 1;
      end
    join
  endtask

  virtual task run_parallel_seq(ref bit base_vseq_done);
    // Override with real parallel sequence
    `uvm_fatal(`gfn, "please override this method!")
  endtask

  virtual task wait_clk_or_reset(int wait_clks);
    repeat(wait_clks) begin
      @(posedge cfg.clk_rst_vif.clk);
      if (cfg.under_reset) break;
    end
  endtask

endclass
