// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// SW starts operation and HW will set cfgen=0 to prevent write to registers gated by cfgen
// Test those registers can't be written during OpWip
// Also check cfgen value is updated by design correctly
class keymgr_cfgen_vseq extends keymgr_random_vseq;
  `uvm_object_utils(keymgr_cfgen_vseq)
  `uvm_object_new

  virtual task body();
    bit regular_vseq_done;
    fork
      write_cfgen_gate_regs_during_op_wip(regular_vseq_done);
      begin
        super.body();
        // let the unblocking thread finish before ending this seq
        regular_vseq_done = 1;
      end
    join
  endtask : body

  task write_cfgen_gate_regs_during_op_wip(ref bit regular_vseq_done);
    // since it's very timing sensitive, backdoor wait op_status.
    // randomly add 0-100 cycle delay, backdoor check op_status again
    // When status is still OpWip, call write_cfgen_gated_reg and the write will be ignored
    while (!regular_vseq_done) begin
      bit [TL_DW-1:0] op_status_val, cfgen_val;
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

      // 50% to read cfgen and check in scb
      if ($urandom_range(0, 1)) csr_rd(ral.cfgen, cfgen_val);

      // writing during cfgen is timing sensitive
      // 1. make sure no other thread is accessing register
      // 2. use backdoor check op_status again in case it's not OpWip after front-door read
      // 3. make sure done isn't high, because if done is high, next cycle status won't be WIP
      wait_no_outstanding_access();
      csr_rd(ral.op_status, op_status_val, .backdoor(1));
      if (op_status_val == keymgr_pkg::OpWip && cfg.keymgr_vif.kmac_data_rsp.done) begin
        write_cfgen_gated_reg();
      end
    end
  endtask

  virtual task write_cfgen_gated_reg();
    bit [TL_DW-1:0] val = $urandom;

    `uvm_info(`gfn, "Write cfgen gated reg, and this write should be ignored", UVM_HIGH)
    // since it's timing sensitive, only write one of these reg
    randcase
      1: csr_wr(ral.control,            val);
      1: csr_wr(ral.key_version,        val);
      1: csr_wr(ral.sw_binding_0,       val);
      1: csr_wr(ral.sw_binding_1,       val);
      1: csr_wr(ral.sw_binding_2,       val);
      1: csr_wr(ral.sw_binding_3,       val);
      1: csr_wr(ral.salt_0,             val);
      1: csr_wr(ral.salt_1,             val);
      1: csr_wr(ral.salt_2,             val);
      1: csr_wr(ral.salt_3,             val);
    endcase
  endtask : write_cfgen_gated_reg
endclass : keymgr_cfgen_vseq
