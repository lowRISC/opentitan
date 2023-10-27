// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// 'Memory-to-memory' DMA transfers
class dma_memory_vseq extends dma_generic_vseq;
  `uvm_object_utils(dma_memory_vseq)
  `uvm_object_new

  // Randomization that restricts the DMA configuration to memory-to-memory transfers only
  virtual function void randomize_item(ref dma_seq_item dma_config);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(dma_config,
      handshake == 1'b0;) // Disable hardware handshake mode
    `uvm_info(`gfn, $sformatf("DMA: Randomized a new transaction:%s",
                              dma_config.convert2string()), UVM_HIGH)
  endfunction

  virtual task body();
    super.body();
  endtask : body
endclass
