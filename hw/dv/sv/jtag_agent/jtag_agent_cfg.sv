// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_agent_cfg extends dv_base_agent_cfg;

// interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual jtag_if vif;

  `uvm_object_utils_begin(jtag_agent_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // control tck
  function void set_tck_en(bit en);
    vif.tck_en = en;
  endfunction

  // assert trst_n for a number of cycles
  task do_trst_n(int cycles = $urandom_range(5, 20));
    vif.do_trst_n(cycles);
  endtask

endclass
