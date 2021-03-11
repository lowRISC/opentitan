// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_smoke_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_smoke_vseq)

  `uvm_object_new

  task body();
    // Ensure es_entropy is 0 before enabling
    csr_rd_check(.ptr(ral.entropy_data), .compare_value(1'b0));

    // Change entropy rate
    csr_wr(.csr(ral.rate), .value('h8));

    // Route to ENTROPY_DATA register
    csr_wr(.csr(ral.entropy_control), .value(1'b1));

    // Enable entropy_src - lfsr mode
    csr_wr(.csr(ral.conf), .value(2'b10));

    // Wait for entropy_valid interrupt
    csr_spinwait(.ptr(ral.intr_state.es_entropy_valid), .exp_data(1'b1));

    // Read entropy_data register (384/32=12 times) and expect POR_ENTROPY
    for (int i = 0; i < 12; i++) begin
      csr_rd_check(.ptr(ral.entropy_data), .compare_value(POR_ENTROPY[i]));
    end

    // Ensure entropy_valid interrupt bit set
    csr_rd_check(.ptr(ral.intr_state), .compare_value(1'b1));

    // Clear entropy_valid interrupt bit
    csr_wr(.csr(ral.intr_state), .value(1'b1));

    // Ensure entropy_valid interrupt bit cleared
    csr_rd_check(.ptr(ral.intr_state), .compare_value(1'b0));

  endtask : body

endclass : entropy_src_smoke_vseq
