// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test flash access disable feature by
// Global escalation : Set lc_escalate_en to On
// sw command (flash_ctrl.DIS)
class flash_ctrl_disable_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_disable_vseq)
  `uvm_object_new


  virtual task body();
    bit exp_err;

    $assertoff(0, "tb.dut.u_lc_escalation_en_sync");
    send_rand_ops();
    set_flash_disable(exp_err);

    if (exp_err) begin
       `uvm_info("SEQ", $sformatf("disable is set"), UVM_MEDIUM)
       csr_utils_pkg::wait_no_outstanding_access();
       cfg.m_tl_agent_cfg.check_tl_errs = 0;
    end
    `uvm_info("SEQ", $sformatf("disable txn start"), UVM_MEDIUM)
    // mp error or tlul error expected

    // Wait until disable is set.
    cfg.clk_rst_vif.wait_clks(10);
    send_rand_ops(1, exp_err);

    `DV_CHECK_EQ(cfg.tlul_core_obs_cnt, cfg.tlul_core_exp_cnt)
  endtask // body

  task set_flash_disable(ref bit exp_err);
    bit is_disable = 0;
    randcase
      1: begin
        cfg.flash_ctrl_vif.lc_escalate_en =
          get_rand_lc_tx_val(.t_weight(1), .f_weight(1), .other_weight(4));
        is_disable = (cfg.flash_ctrl_vif.lc_escalate_en != lc_ctrl_pkg::Off);
      end
      1: begin
        mubi4_t dis_val;
        dis_val = get_rand_mubi4_val(.t_weight(1), .f_weight(1), .other_weight(4));
        csr_wr(.ptr(ral.dis), .value(dis_val));
        // DIS acts as true if program value is not 4b0xxx or xxx0.
        // However, there is additional routine in flash_ctrl_lcmgr makes
        // disable flash when dis_val is not mubi_false.
        is_disable = (dis_val != prim_mubi_pkg::MuBi4False);
      end
    endcase // randcase
    exp_err = is_disable;
  endtask
endclass
