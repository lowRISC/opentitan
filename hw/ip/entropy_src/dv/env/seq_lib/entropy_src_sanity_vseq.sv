// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class entropy_src_sanity_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_sanity_vseq)

  `uvm_object_new

  task body();
    // Ensure es_entropy is 0 before enabling
    csr_rd_check(.ptr(ral.es_entropy), .compare_value(1'b0));

    // Set FIFO Threshold
    csr_wr(.csr(ral.es_thresh), .value(1'b1));

    // Enable entropy_src
    csr_wr(.csr(ral.es_conf), .value(1'b1));

    // Wait for entropy_valid interrupt
    csr_spinwait(.ptr(ral.intr_state.es_entropy_valid), .exp_data(1'b1));

    // Expect POR_ENTROPY with POR_SEED
    csr_rd_check(.ptr(ral.es_entropy), .compare_value(POR_ENTROPY));

    // Disable entropy_src
    csr_wr(.csr(ral.es_conf), .value(1'b0));

    // Ensure entropy_valid interrupt bit set
    csr_rd_check(.ptr(ral.intr_state), .compare_value(1'b1));

    // Clear entropy_valid interrupt bit
    csr_wr(.csr(ral.intr_state), .value(1'b1));

    // Ensure entropy_valid interrupt bit cleared
    csr_rd_check(.ptr(ral.intr_state), .compare_value(1'b0));

  endtask : body

endclass : entropy_src_sanity_vseq
