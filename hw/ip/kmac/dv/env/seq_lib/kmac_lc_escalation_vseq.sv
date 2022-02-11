// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_lc_escalation_vseq extends kmac_app_vseq;

  `uvm_object_utils(kmac_lc_escalation_vseq)
  `uvm_object_new

  virtual task body();
    fork begin : isolation_fork
      fork
        begin
          super.body();
        end
        begin
          cfg.clk_rst_vif.wait_clks($urandom_range(1, 500_000));
          cfg.kmac_vif.drive_lc_escalate(
              get_rand_lc_tx_val(.t_weight(1), .f_weight(0), .other_weight(1)));
          cfg.en_scb = 0;
          check_fatal_alert_nonblocking("fatal_fault_err");
        end
      join_any;
      wait_no_outstanding_access();
      disable fork;
    end join

    // Check only if lc_escalate_en is not `Off`.
    if (cfg.en_scb == 0) begin
      kmac_pkg::kmac_cmd_e rand_cmd;
      bit [7:0] share[];
      cfg.clk_rst_vif.wait_clks($urandom_range(5, 100));

      // Randomly turns off lc_escalate_en.
      if ($urandom_range(0, 1)) begin
        cfg.clk_rst_vif.wait_clks(10);
        cfg.kmac_vif.drive_lc_escalate(lc_ctrl_pkg::Off);
      end

      `DV_CHECK_RANDOMIZE_FATAL(this)
      `DV_CHECK_STD_RANDOMIZE_FATAL(rand_cmd)

      // Check if kmac will accept any SW request.
      check_lc_escalate_status();
      kmac_init(0);
      set_prefix();
      write_key_shares();
      provide_sw_entropy();
      issue_cmd(rand_cmd);
      write_msg(msg);
      check_lc_escalate_status();
      read_digest_chunk(KMAC_STATE_SHARE0_BASE, keccak_block_size, share);
      foreach (share[i]) `DV_CHECK_EQ_FATAL(share[i], '0)
      read_digest_chunk(KMAC_STATE_SHARE1_BASE, keccak_block_size, share);
      foreach (share[i]) `DV_CHECK_EQ_FATAL(share[i], '0)

      // TODO: Add checking for kmac app request.
    end
  endtask

  virtual task post_start();
    expect_fatal_alerts = 1;
    super.post_start();
  endtask

  virtual task check_lc_escalate_status();
    csr_rd_check(.ptr(ral.status.alert_fatal_fault), .compare_value(1'b1));
    csr_rd_check(.ptr(ral.status.sha3_idle), .compare_value(1'b0));
    // TODO(#10804): confirm with designer if we need an error code here.
    // csr_rd_check(.ptr(ral.err_code), .compare_value(?));
  endtask

endclass
