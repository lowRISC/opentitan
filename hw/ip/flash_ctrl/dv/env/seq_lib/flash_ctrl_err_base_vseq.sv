// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Base sequence for fault tests
class flash_ctrl_err_base_vseq extends flash_ctrl_rw_vseq;
  `uvm_object_utils(flash_ctrl_err_base_vseq)
  `uvm_object_new

  task body();
    int    state_timeout_ns = 100000; // 100us
    fork
      begin
        super.body();
      end
      begin
        run_error_event();
      end
    join
    cfg.seq_cfg.disable_flash_init = 1;
    cfg.seq_cfg.en_init_keys_seeds = 0;
    apply_reset();
    csr_wr(.ptr(ral.init), .value(1));
    `uvm_info(`gfn,"Test: OTP",UVM_LOW)
    otp_model();
    `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.rd_buf_en == 1);,
                 "Timed out waiting for rd_buf_en",
                 state_timeout_ns)
    cfg.clk_rst_vif.wait_clks(10);
  endtask

  virtual task run_error_event(); endtask

  task check_fault(input uvm_object ptr,
                   input uvm_reg_data_t exp_data = 1);
    `uvm_info(`gfn, "err assert is done", UVM_MEDIUM)
    csr_spinwait(.ptr(ptr), .exp_data(exp_data));
    `uvm_info(`gfn, "csr wait is done is done", UVM_MEDIUM)
  endtask

endclass
