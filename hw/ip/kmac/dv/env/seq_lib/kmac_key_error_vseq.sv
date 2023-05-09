// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Trigger KeyNotValid error by not providing valid keymgr key during kmac transaction.
// ICEBOX(#10704): current RTL only supports this error in app mode.
class kmac_key_error_vseq extends kmac_app_vseq;

  `uvm_object_utils(kmac_key_error_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[1:20]};
  }

  virtual task body();
    kmac_pkg::err_t kmac_err;
    cfg.en_scb = 0;
    check_keymgr_rsp_nonblocking();

    for (int i = 0; i < num_trans; i++) begin
      bit [7:0] share0[];
      bit [7:0] share1[];

      `uvm_info(`gfn, $sformatf("iteration: %0d/%0d", i, num_trans), UVM_LOW)

      `DV_CHECK_RANDOMIZE_FATAL(this)
      kmac_err_type = kmac_pkg::ErrKeyNotValid;
      kmac_err = '{valid: 1'b1,
                   code: kmac_pkg::ErrKeyNotValid,
                   info: '0};
      app_mode = AppKeymgr;

      kmac_init();
      `uvm_info(`gfn, "kmac_init done", UVM_LOW)

      set_prefix();

      write_key_shares();

      if (cfg.enable_masking && entropy_mode == EntropyModeSw) begin
        `uvm_info(`gfn, "providing SW entropy", UVM_HIGH)
        provide_sw_entropy();
      end

      fork begin : isolation_fork
        fork
          send_kmac_app_req(app_mode);
          wait (cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_req.valid);
        join_any;
        disable fork;
      end join

      // Wait randomly time before check status and issue err_processed.
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 10_000));

      // ICEBOX(#10835): Check with designer if sha3_idle should be set to 0.
      csr_rd_check(.ptr(ral.status), .compare_value(ral.status.get_reset()));
      csr_rd_check(.ptr(ral.err_code), .compare_value(kmac_err));
      check_err();
    end

    // ICEBOX: enable scb and run normal sequence, then add this sequence to stress_all sequence.
    // cfg.en_scb = 1;
    // super.body();
  endtask

  // While scb is not enabled, this task checks that during KeyNotValid error case, app interface
  // to keymgr will always return 0 digest value, and assert error when the process is done.
  virtual task check_keymgr_rsp_nonblocking();
    fork begin
      while (cfg.en_scb == 0) begin
        wait (cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_rsp.ready == 1);
        `DV_CHECK_EQ(cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_rsp.digest_share0, '0)
        `DV_CHECK_EQ(cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_rsp.digest_share1, '0)
        wait (cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_rsp.ready == 0);
      end
    end join_none

    fork begin
      while (cfg.en_scb == 0) begin
        wait (cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_rsp.done == 1);
        `DV_CHECK_EQ(cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_rsp.error, 1)
        wait (cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_rsp.done == 0);
      end
    end join_none
  endtask

endclass
