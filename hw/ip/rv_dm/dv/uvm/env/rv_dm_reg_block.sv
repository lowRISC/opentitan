// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_reg_block extends dv_base_reg_block;
  `uvm_object_utils(rv_dm_reg_block)

  function new(string name = "rv_dm_reg_block", int has_coverage = UVM_NO_COVERAGE);
    super.new(name, has_coverage);
  endfunction : new

  virtual function void build(uvm_reg_addr_t base_addr);
    `uvm_info(`gfn, "no-ral", UVM_LOW)
  endfunction : build

endclass : rv_dm_reg_block
