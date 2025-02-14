// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_smoke_vseq extends ac_range_check_base_vseq;
  `uvm_object_utils(ac_range_check_smoke_vseq)

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : ac_range_check_smoke_vseq


function ac_range_check_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task ac_range_check_smoke_vseq::body();
  `uvm_error(`gfn, "FIXME")
endtask : body
