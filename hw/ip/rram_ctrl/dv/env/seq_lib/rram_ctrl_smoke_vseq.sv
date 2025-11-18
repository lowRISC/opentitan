// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_smoke_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_smoke_vseq)

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : rram_ctrl_smoke_vseq


function rram_ctrl_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task rram_ctrl_smoke_vseq::body();
 // TODO temporary just to check RW to a register
  uvm_reg_data_t data;
  `uvm_info(`gfn, "Test to write to a register", UVM_LOW)

  csr_rd(ral.scratch, data);
  `uvm_info(`gfn, $sformatf("Read data: 0x%0h", data), UVM_LOW)
  csr_wr(ral.scratch, 32'hDEADBEEF);
  csr_rd(ral.scratch, data);
  `uvm_info(`gfn, $sformatf("Read data: 0x%0h", data), UVM_LOW)
endtask : body
