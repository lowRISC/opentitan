// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Line loopback (rx -> tx) sequence
class i2c_llpbk_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_llpbk_vseq)
  `uvm_object_new

  virtual task body();
    int loopback_wait_timeout_ns = 1_000_000; // 1ms
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

    `JDBG(("LB seq loopback start addr:%x", target_addr0))
    cfg.m_i2c_agent_cfg.loopback_num_bytes = 8;
    cfg.m_i2c_agent_cfg.loopback_st = 1;


    wait(cfg.m_i2c_agent_cfg.loopback_st == 0);
    `JDBG(("LB seq loopback end"))
  endtask
endclass
