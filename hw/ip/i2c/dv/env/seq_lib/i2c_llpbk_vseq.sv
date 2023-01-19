// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Line loopback (rx -> tx) sequence
class i2c_llpbk_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_llpbk_vseq)
  `uvm_object_new

  virtual task body();
    int loopback_wait_timeout_ns = 1000_000_000; // 1s
    if (cfg.m_i2c_agent_cfg.if_mode == Device) begin
       i2c_init(Host);
    end else begin
       i2c_init(Device);
    end

    get_timing_values();
    program_registers();
    ral.ctrl.llpbk.set(1'b1);
    csr_update(ral.ctrl);
    // target mode
    cfg.m_i2c_agent_cfg.lb_addr[7:1] = target_addr0;

    `uvm_info("seq", $sformatf("LB seq loopback start addr:%x", target_addr0), UVM_MEDIUM)
    cfg.m_i2c_agent_cfg.loopback_num_bytes = i2c_reg_pkg::FifoDepth;
    cfg.m_i2c_agent_cfg.loopback_st = 1;
    `DV_WAIT(cfg.m_i2c_agent_cfg.loopback_st == 0,, loopback_wait_timeout_ns,
             "loopback_sequence_wait")
  endtask
endclass
