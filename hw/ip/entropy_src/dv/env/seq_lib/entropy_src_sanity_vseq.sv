// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class entropy_src_sanity_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_sanity_vseq)

  `uvm_object_new

  task body();
    bit [TL_DW-1:0] es_seed, rd_data;

    // Get es_seed
    csr_rd(.ptr(ral.es_seed), .value(es_seed));

    // Enable entropy_src
    csr_wr(.csr(ral.es_conf), .value(1'b1));

    // Wait for entropy_rdy
    //mwb: removed for now: csr_spinwait(.ptr(ral.es_status.entropy_rdy), .exp_data(1));

    // Wait for entropy_valid interrupt
    csr_spinwait(.ptr(ral.intr_state.es_entropy_valid), .exp_data(1));

    // Expect 1st entropy to be es_seed
    csr_rd_check(.ptr(ral.es_entropy), .compare_value(es_seed));

    // Disable entropy_src
    csr_wr(.csr(ral.es_conf), .value(1'b0));

    // Clear/Validate entropy_valid interrupt bit
    csr_wr(.csr(ral.intr_state), .value(1'b1));

    // Ensure entropy_valid interrupt bit cleared
    csr_rd_check(.ptr(ral.intr_state), .compare_value(0));
    
  endtask : body

endclass : entropy_src_sanity_vseq
