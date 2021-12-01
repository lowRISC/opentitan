// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_smoke_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_smoke_vseq)

  `uvm_object_new

  int rng_count = 0;

  virtual function queue_of_rng_val_t generate_rng_data(int quad_cnt);
    queue_of_rng_val_t result;

    for (int i = 0; i < quad_cnt; i++) begin
      result.push_back(4'(rng_count));
      rng_count++;
    end

    return result;
  endfunction

  task body();

    init_rng_push_seq;

    // Wait for entropy_valid interrupt
    csr_spinwait(.ptr(ral.intr_state.es_entropy_valid), .exp_data(1'b1));

    // Read and check entropy
    for (int i = 0; i < entropy_src_pkg::CSRNG_BUS_WIDTH/TL_DW; i++) begin
      bit [TL_DW-1:0] entropy_tlul;
      csr_rd(.ptr(ral.entropy_data), .value(entropy_tlul));
    end

    // Ensure entropy_valid interrupt bit set
    csr_rd_check(.ptr(ral.intr_state), .compare_value(1'b1));

    // Clear entropy_valid interrupt bit
    csr_wr(.ptr(ral.intr_state), .value(1'b1));

    // Ensure entropy_valid interrupt bit cleared
    csr_rd_check(.ptr(ral.intr_state), .compare_value(1'b0));

  endtask : body

endclass : entropy_src_smoke_vseq
