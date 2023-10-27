// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Stress all DMA configurations and transfer properties, valid or invalid
class dma_stress_all_vseq extends dma_generic_vseq;
  `uvm_object_utils(dma_stress_all_vseq)
  `uvm_object_new

  // Constrain number of iterations and transactions in each iteration
  constraint transactions_c {num_txns inside {[10:40]};}
  constraint num_iters_c {num_iters inside {[5:20]};}

  // The functionality of this vseq is implemented in `dma_generic_vseq` and restricted
  // to 'hardware handshaking' transfers in `dma_handshake_vseq`
  virtual task body();
    `uvm_info(`gfn, "DMA: Starting stress all Sequence", UVM_LOW)
    super.body();
    `uvm_info(`gfn, "DMA: Completed stress all Sequence", UVM_LOW)
  endtask : body
endclass
