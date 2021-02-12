// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// During DAI operation HW will set direct_access_regwen=0 to prevent write to registers that
// affect DAI interface
// Test those registers can't be written during OTP power up operation
// Also check regwen value is updated by design correctly
class otp_ctrl_regwen_vseq extends otp_ctrl_smoke_vseq;
  `uvm_object_utils(otp_ctrl_regwen_vseq)
  `uvm_object_new

  virtual task body();
    bit regular_vseq_done;
    fork
      write_regwen_gate_regs_during_otp_busy(regular_vseq_done);
      begin
        super.body();
        // let the unblocking thread finish before ending this seq
        regular_vseq_done = 1;
      end
    join
  endtask : body

  virtual task write_regwen_gate_regs_during_otp_busy(ref bit regular_vseq_done);
    while (!regular_vseq_done) begin
      bit [TL_DW-1:0] regwen_val, status_val;
      uint delay;
      wait (cfg.otp_ctrl_vif.pwr_otp_done_o === 0 && !cfg.under_reset || regular_vseq_done);
      if (regular_vseq_done) return;

      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(delay,
                                         delay dist {[0:10]    :/ 1,
                                                     [11:100]  :/ 1,
                                                     [101:500] :/ 1};)
      cfg.clk_rst_vif.wait_clks(delay);

      if ($urandom_range(0, 1)) begin
        if (!cfg.under_reset) csr_rd(ral.direct_access_regwen, regwen_val);
      end

      // writing during DAI operation is timing sensitive
      // 1. make sure other thread is not accessing registers
      // 2. use backdoor check otp init is not done and is not under reset
      wait_no_outstanding_access();
      if (cfg.otp_ctrl_vif.pwr_otp_done_o === 0 && !cfg.under_reset) begin
        write_and_check_regwen_lockable_reg();
      end
      wait (cfg.otp_ctrl_vif.pwr_otp_done_o === 1 || cfg.under_reset || regular_vseq_done);
    end
  endtask

  virtual task write_and_check_regwen_lockable_reg();
    bit [TL_DW-1:0] val = $urandom;
    // since it's timing sensitive, only write one of these reg
    dv_base_reg     lockable_reg;
    dv_base_reg_field     lockable_flds[$];

    ral.direct_access_regwen.get_lockable_flds(lockable_flds);
    lockable_flds.shuffle();
    lockable_reg = lockable_flds[0].get_dv_base_reg_parent();

    `uvm_info(`gfn, $sformatf("Write regwen lockable reg %0s, and this write should be ignored",
                              lockable_reg.get_name()), UVM_HIGH)
    csr_wr(lockable_reg, val);
    csr_rd(lockable_reg, val); // checking is done with scb
  endtask : write_and_check_regwen_lockable_reg

endclass
