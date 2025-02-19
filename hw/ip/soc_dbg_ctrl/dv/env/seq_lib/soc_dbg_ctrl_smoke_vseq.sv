// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class soc_dbg_ctrl_smoke_vseq extends soc_dbg_ctrl_base_vseq;
  `uvm_object_utils(soc_dbg_ctrl_smoke_vseq)

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : soc_dbg_ctrl_smoke_vseq


function soc_dbg_ctrl_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task soc_dbg_ctrl_smoke_vseq::body();
  `uvm_error(`gfn, "FIXME")
endtask : body
