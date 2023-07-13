// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence to verify the countermeasure(s) PC.CTRL_FLOW.REDUN.

class otbn_pc_ctrl_flow_redun_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_pc_ctrl_flow_redun_vseq)
  `uvm_object_new

  task body();
    do_end_addr_check = 0;
    fork
      begin
        super.body();
      end
      begin
        corrupt_prefetch_addr();
      end
    join
  endtask: body

  task corrupt_prefetch_addr();
    bit imem_rvalid;
    bit insn_fetch_req_valid;
    bit prefetch_ignore_err;
    bit [11:0] good_addr;
    bit [11:0] bad_addr;
    bit [11:0] mask;
    bit [31:0] err_val = 32'd1 << 20;
    string addr_path = "tb.dut.u_otbn_core.u_otbn_instruction_fetch.insn_prefetch_addr";

    do begin
      @(cfg.clk_rst_vif.cb);
      if (!uvm_hdl_read("tb.dut.u_otbn_core.u_otbn_instruction_fetch.imem_rvalid_i", imem_rvalid))
        `uvm_fatal(`gfn, "failed to read imem_rvalid_i");
      if (!uvm_hdl_read("tb.dut.u_otbn_core.u_otbn_instruction_fetch.insn_fetch_req_valid_raw_i",
                        insn_fetch_req_valid))
        `uvm_fatal(`gfn, "failed to read insn_fetch_req_valid_raw_i");
      if (!uvm_hdl_read("tb.dut.u_otbn_core.u_otbn_instruction_fetch.prefetch_ignore_errs_i",
                        prefetch_ignore_err))
        `uvm_fatal(`gfn, "failed to read prefetch_ignore_errs_i");
    end while(!(imem_rvalid & insn_fetch_req_valid & !prefetch_ignore_err));
    `DV_CHECK_FATAL(uvm_hdl_read(addr_path, good_addr));
    // Mask to corrupt 1 to 2 bits of the prefetch addr
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)
    bad_addr = good_addr ^ mask;
    `DV_CHECK_FATAL(uvm_hdl_force(addr_path, bad_addr) == 1);
    `uvm_info(`gfn, "injecting bad internal state error into ISS", UVM_HIGH)
    cfg.model_agent_cfg.vif.send_err_escalation(err_val);
    wait(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked);
    `DV_CHECK_FATAL(uvm_hdl_release(addr_path) == 1);
    reset_if_locked();
  endtask

endclass : otbn_pc_ctrl_flow_redun_vseq
