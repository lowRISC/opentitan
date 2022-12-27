// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Line loopback (rx -> tx) sequence
class i2c_llpbk_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_llpbk_vseq)
  `uvm_object_new

  virtual task body();
    ral.ctrl.llpbk.set(1'b1);
    csr_update(ral.ctrl);
    `JDBG(("LB seq loopback start"))
    cfg.m_i2c_agent_cfg.loopback_st = 1;

  endtask
endclass
