// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence triggers std_fault_status.lcmgr_intg_err by force
class flash_ctrl_lcmgr_intg_vseq extends flash_ctrl_err_base_vseq;
  `uvm_object_utils(flash_ctrl_lcmgr_intg_vseq)
  `uvm_object_new

  task run_main_event;
    cfg.seq_cfg.disable_flash_init = 1;
    cfg.seq_cfg.en_init_keys_seeds = 0;
    apply_reset();
    init_controller(.non_blocking(1));
  endtask // init_controller

   // fatal_std_err
   task run_error_event();
     int wait_timeout_ns = 50_000;
     string path = "tb.dut.u_flash_hw_if.rdata_i[38:32]";
     int    err_intg = $urandom_range(0, 127);

     `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.hw_rvalid == 1);,
                  , wait_timeout_ns)
     cfg.scb_h.expected_alert["fatal_std_err"].expected = 1;
     cfg.scb_h.expected_alert["fatal_std_err"].max_delay = 2000;
     cfg.scb_h.exp_alert_contd["fatal_std_err"] = 10000;

     $assertoff(0, "tb.dut.u_flash_mp.NoReqWhenErr_A");
     #0;
     @(posedge cfg.flash_ctrl_vif.hw_rvalid);
     `DV_CHECK(uvm_hdl_force(path, err_intg))
     // Make sure this is not too long.
     // If this is too long, it will causes other fatal errors.
     cfg.clk_rst_vif.wait_clks(5);
     `DV_CHECK(uvm_hdl_release(path))
     collect_err_cov_status(ral.std_fault_status);
     csr_rd_check(.ptr(ral.std_fault_status.lcmgr_intg_err), .compare_value(1));
   endtask
endclass // flash_ctrl_lcmgr_intg_vseq
