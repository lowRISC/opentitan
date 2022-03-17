// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will randomly issue lc_escalate_en during or after partition is locked.
// After lc_escalate_en is On, this sequence will continue run base sequence to check if all state
// machines are locked to `ErrorSt`.

class otp_ctrl_parallel_lc_esc_vseq extends otp_ctrl_dai_lock_vseq;
  `uvm_object_utils(otp_ctrl_parallel_lc_esc_vseq)

  `uvm_object_new
  bit [lc_ctrl_pkg::TxWidth-1:0] lc_esc_on_val;

  constraint lc_esc_on_c {lc_esc_on_val != lc_ctrl_pkg::Off;}

  // This sequence will kill super.body sequence once lc_escalate_en is On. Disable these interface
  // requests to avoid sequencer error.
  constraint key_lc_reqs_c {
    do_req_keys == 0;
    do_lc_trans == 0;
  }

  virtual task body();
    fork
      begin : isolation_fork
        fork
          rand_wait_csr_no_outstanding();
          super.body();
        join_any;
        disable fork;
        set_lc_esc_and_check();
      end
    join
  endtask

  virtual task rand_wait_csr_no_outstanding();
    wait(cfg.under_reset == 0);
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 10_000));
    wait_no_outstanding_access();
  endtask

  virtual task set_lc_esc_and_check();
    // Random issue key requests before lc_esc_en is issued.
    randcase
      1: req_otbn_key(0);
      1: req_flash_addr_key(0);
      1: req_flash_data_key(0);
      1: req_all_sram_keys(0);
      1: req_lc_transition(0, 0);
    endcase
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 50));

    cfg.otp_ctrl_vif.drive_lc_escalate_en(get_rand_lc_tx_val(.f_weight(0)));

    // TODO: in alert_esc_monitor, makes it auto-response like push-pull agent
    if (en_auto_alerts_response && cfg.list_of_alerts.size()) run_alert_rsp_seq_nonblocking();

    // Wait 5 clock cycles until async lc_escalate_en propogate to each state machine.
    cfg.clk_rst_vif.wait_clks(5);

    // After LC_escalate is On, we trigger the dai_lock_vseq to check interfaces will return
    // default values and the design won't hang.
    otp_ctrl_dai_lock_vseq::body();
  endtask

  virtual task post_start();
    expect_fatal_alerts = 1;
    cfg.otp_ctrl_vif.drive_lc_escalate_en(lc_ctrl_pkg::Off);
    super.post_start();
  endtask
endclass
