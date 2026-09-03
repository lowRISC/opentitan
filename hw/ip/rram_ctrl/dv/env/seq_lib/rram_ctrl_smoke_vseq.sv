// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Minimal smoke test: brings the DUT out of reset (via dut_init()/rram_ctrl_init()) and does
// nothing else. Real content is still TODO (writes, reads, host access, etc.).
class rram_ctrl_smoke_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_smoke_vseq)

  extern function new(string name="");
  extern task body();
endclass : rram_ctrl_smoke_vseq

function rram_ctrl_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task rram_ctrl_smoke_vseq::body();
  // TODO: add real tests.
endtask : body
