// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_lc_escalation_vseq extends kmac_app_vseq;

  `uvm_object_utils(kmac_lc_escalation_vseq)
  `uvm_object_new

  virtual function void disable_asserts();
    $assertoff(0,
      "tb.dut.gen_entropy.u_prim_sync_reqack_data.u_prim_sync_reqack.SyncReqAckAckNeedsReq");
    $assertoff(0, "tb.edn_if[0].ReqHighUntilAck_A");
    $assertoff(0, "tb.edn_if[0].AckAssertedOnlyWhenReqAsserted_A");
  endfunction

  virtual task pre_start();
    super.pre_start();
    if (cfg.enable_masking) disable_asserts();
  endtask

  virtual task body();
    fork begin : isolation_fork
      fork
        begin
          super.body();
        end
        begin
          if ($urandom_range(0, 4) == 4) begin
            cfg.clk_rst_vif.wait_clks($urandom_range(1, 100_000));
          end else begin
            `DV_SPINWAIT_EXIT(wait(cfg.kmac_vif.idle_o != prim_mubi_pkg::MuBi4True);,
                              cfg.clk_rst_vif.wait_clks(10_000_000););
            cfg.clk_rst_vif.wait_clks($urandom_range(0, 200));
          end
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
      cfg.clk_rst_vif.wait_clks($urandom_range(5, 100));

      // Randomly turns off lc_escalate_en.
      if ($urandom_range(0, 1)) begin
        cfg.clk_rst_vif.wait_clks(10);
        cfg.kmac_vif.drive_lc_escalate(lc_ctrl_pkg::Off);
      end

      `DV_CHECK_RANDOMIZE_FATAL(this)

      check_lc_escalate_status();

      // Check if kmac will accept any SW request.
      kmac_sw_lock_check();

      // Checking for kmac app request.
      kmac_app_lock_check();
    end
  endtask

  virtual task post_start();
    expect_fatal_alerts = 1;
    cfg.kmac_vif.drive_lc_escalate(lc_ctrl_pkg::Off);
    super.post_start();
  endtask

  virtual task check_lc_escalate_status();
    csr_rd_check(.ptr(ral.status.alert_fatal_fault), .compare_value(1'b1));
    csr_rd_check(.ptr(ral.status.sha3_idle), .compare_value(1'b0));
    // ICEBOX(#10804): confirm with designer if we need an error code here.
    // csr_rd_check(.ptr(ral.err_code), .compare_value(?));
  endtask

endclass
