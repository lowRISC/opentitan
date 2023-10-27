// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence is used to run register tests. The type of register test to be run can
// be selected via run args.
// run_common_vseq_wrapper is inherited from cip_base_vseq which has all the common sequences
// that can be run for a CIP compliant IP.
class dma_common_vseq extends dma_base_vseq;
  `uvm_object_utils(dma_common_vseq)
  `uvm_object_new

  constraint num_trans_c { num_trans inside {[1:2]}; }

  // for this vseq, $value$plusargs "+en_scb=0" is defined in dma_sim_cfg.hjson
  // disable dma_monitor and dma_scoreboard since they can not handle this test

  virtual task body();
    `uvm_info(`gfn, "\n--> start of dma_common_vseq", UVM_DEBUG)
    run_common_vseq_wrapper(num_trans);
    `uvm_info(`gfn, "\n--> end of dma_common_vseq", UVM_DEBUG)
  endtask : body

endclass : dma_common_vseq
