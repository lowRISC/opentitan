// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// rng_entropy test vseq
class entropy_src_rng_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_rng_vseq)

  `uvm_object_new

  task body();
    // TODO: Temporary for developing rng_agent
    // Enable/Disable rng
    csr_wr(.csr(ral.conf), .value(5'h10));    
    csr_wr(.csr(ral.conf), .value(5'h00));    
    csr_wr(.csr(ral.conf), .value(5'h10));    
    csr_wr(.csr(ral.conf), .value(5'h00));    
    csr_wr(.csr(ral.conf), .value(5'h10));    
    csr_wr(.csr(ral.conf), .value(5'h00));    
  endtask : body

endclass : entropy_src_rng_vseq
