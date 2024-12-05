// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// 'Hardware handshake' DMA transfers
class dma_handshake_vseq extends dma_generic_vseq;
  `uvm_object_utils(dma_handshake_vseq)
  `uvm_object_new

  // Randomization that restricts the DMA configuration to hardware handshake transfers only
  virtual function void randomize_item(ref dma_seq_item dma_config);
    // Limit all parameters to 4B alignment
    `DV_CHECK_RANDOMIZE_WITH_FATAL(dma_config,
      handshake == 1'b1;) // Enable hardware handhake mode
    `uvm_info(`gfn, $sformatf("DMA: Randomized a new transaction:%s",
                              dma_config.convert2string()), UVM_HIGH)
  endfunction

  virtual task body();
    super.body();
  endtask : body
endclass
