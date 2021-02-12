// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// SW starts operation and HW will set cfg_regwen=0 to prevent write to registers gated by cfg_regwen
// Test those registers can't be written during OpWip
// Also check cfg_regwen value is updated by design correctly
class keymgr_cfg_regwen_vseq extends keymgr_random_vseq;
  `uvm_object_utils(keymgr_cfg_regwen_vseq)
  `uvm_object_new

  virtual task body();
    bit regular_vseq_done;
    fork
      write_cfg_regwen_gate_regs_during_op_wip(regular_vseq_done);
      begin
        super.body();
        // let the unblocking thread finish before ending this seq
        regular_vseq_done = 1;
      end
    join
  endtask : body

  task write_cfg_regwen_gate_regs_during_op_wip(ref bit regular_vseq_done);
    // since it's very timing sensitive, backdoor wait op_status.
    // randomly add 0-100 cycle delay, backdoor check op_status again
    // When status is still OpWip, call write_cfg_regwen_gated_reg and the write will be ignored
    while (!regular_vseq_done) begin
      bit [TL_DW-1:0] op_status_val, cfg_regwen_val;
      uint delay;

      forever begin
        csr_rd(ral.op_status, op_status_val, .backdoor(1));

        if (op_status_val == keymgr_pkg::OpWip) break;
        else if (regular_vseq_done) return;

        cfg.clk_rst_vif.wait_clks(1);
      end

      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(delay,
                                         delay dist {[0:1]    :/ 1,
                                                     [2:10]   :/ 1,
                                                     [11:100] :/ 1};)
      cfg.clk_rst_vif.wait_clks(delay);

      // 50% to read cfg_regwen and check in scb
      if ($urandom_range(0, 1)) csr_rd(ral.cfg_regwen, cfg_regwen_val);

      // writing during cfg_regwen is timing sensitive
      // 1. make sure no other thread is accessing register
      // 2. use backdoor check op_status again in case it's not OpWip after front-door read
      // 3. make sure done isn't high, because if done is high, next cycle status won't be WIP
      wait_no_outstanding_access();
      csr_rd(ral.op_status, op_status_val, .backdoor(1));
      if (op_status_val == keymgr_pkg::OpWip && !cfg.keymgr_vif.kmac_data_rsp.done) begin
        write_and_check_regwen_lockable_reg();
      end
    end
  endtask

  virtual task write_and_check_regwen_lockable_reg();
    bit [TL_DW-1:0]   val = $urandom;
    // since it's timing sensitive, only write one of these reg
    dv_base_reg       lockable_reg;
    dv_base_reg_field lockable_flds[$];

    ral.cfg_regwen.get_lockable_flds(lockable_flds);
    lockable_flds.shuffle();
    lockable_reg = lockable_flds[0].get_dv_base_reg_parent();

    `uvm_info(`gfn, $sformatf("Write regwen lockable reg %0s, and this write should be ignored",
                              lockable_reg.get_name()), UVM_MEDIUM)
    csr_wr(lockable_reg, val);
    // if it's control, wait until OP is done, so that control.start is clear
    if (lockable_reg.get_name() == "control") begin
      csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_pkg::OpWip),
                   .compare_op(CompareOpNe));
    end
    csr_rd(lockable_reg, val); // checking is done with scb
  endtask : write_and_check_regwen_lockable_reg

endclass : keymgr_cfg_regwen_vseq
