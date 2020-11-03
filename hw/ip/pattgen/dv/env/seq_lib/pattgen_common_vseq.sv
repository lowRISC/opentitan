// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_common_vseq extends pattgen_base_vseq;
  `uvm_object_utils(pattgen_common_vseq)
  `uvm_object_new

  constraint num_trans_c { num_trans inside {[1:2]}; }

  // for this vseq, $value$plusargs "+en_scb=0" is defined in pattgen_sim_cfg.hjson
  // disable pattgen_monitor and pattgen_scoreboard since they can not handle this test
  virtual task body();
    `uvm_info(`gfn, "\n--> start of pattgen_common_vseq", UVM_DEBUG)
    run_common_vseq_wrapper(num_trans);
    `uvm_info(`gfn, "\n--> end of pattgen_common_vseq", UVM_DEBUG)
  endtask : body

endclass : pattgen_common_vseq
