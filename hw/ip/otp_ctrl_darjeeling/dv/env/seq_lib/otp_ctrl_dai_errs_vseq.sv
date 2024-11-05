// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// otp_ctrl_dai_errs_vseq is developed to randomly read/write to any address within OTP:
// - A writeblank error will be triggered if write to a non-empty address
// - An access error will be triggered if write to lc partition via DAI interface, or if DAI write
//   to digest addrs for non-sw partitions
class otp_ctrl_dai_errs_vseq extends otp_ctrl_dai_lock_vseq;
  `uvm_object_utils(otp_ctrl_dai_errs_vseq)

  bit[31:0] exp_status;
  `uvm_object_new

  // Only run one transition to avoid dut_init in the sequence. Because write-blank-error can cause
  // otp_init failure.
  constraint num_trans_c {
    num_trans  == 1;
    num_dai_op inside {[100:500]};
  }

  constraint regwens_c {
    check_trigger_regwen_val == 0;
  }

  constraint rd_check_after_wr_c {
    rand_wr == rand_rd;
  }

  function void pre_randomize();
    this.dai_wr_blank_addr_c.constraint_mode(0);
    this.no_access_err_c.constraint_mode(0);
    this.dai_wr_digests_c.constraint_mode(0);
    write_unused_addr = 0;
  endfunction

  task body();
    do_apply_reset = 0;
    if (do_lc_trans && !cfg.otp_ctrl_vif.alert_reqs) begin
      req_lc_transition(do_lc_trans, lc_prog_blocking);
    end
    super.body();
  endtask

  virtual task post_start();
    expect_fatal_alerts = 1;
    do_apply_reset = 1;
    do_otp_ctrl_init = 1;
    super.post_start();
  endtask
endclass
