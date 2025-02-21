// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence is mainly used to run the CSR tests, there is no need to run multiple transactions
// in this sequence. Hence, the constraint is set to run only one transaction.
class soc_dbg_ctrl_common_vseq extends soc_dbg_ctrl_base_vseq;
  `uvm_object_utils(soc_dbg_ctrl_common_vseq)

  // Constraints
  extern constraint num_trans_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task pre_start();
  extern task body();
endclass : soc_dbg_ctrl_common_vseq


constraint soc_dbg_ctrl_common_vseq::num_trans_c {
  num_trans == 1;
}

function soc_dbg_ctrl_common_vseq::new(string name="");
  super.new(name);
endfunction : new

task soc_dbg_ctrl_common_vseq::pre_start();
  do_soc_dbg_ctrl_init = 1'b0;
  super.pre_start();
endtask : pre_start

task soc_dbg_ctrl_common_vseq::body();
  run_common_vseq_wrapper(num_trans);
endtask : body
