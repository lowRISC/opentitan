// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_short_transfer_vseq extends dma_base_vseq;
  `uvm_object_utils(dma_short_transfer_vseq)
  `uvm_object_new

  constraint dma_data_size_c {
    m_dma_total_data_size inside {8,16,32,64};
  }

  constraint dma_range_c {
    (m_dma_range_base % 32) == 0;
    (m_dma_range_limit-m_dma_range_base) inside {2**10, 2**11, 2**12};
  }


  virtual task body();
    `uvm_info( `gfn, "[DMA] Starting Smoke Sequence", UVM_HIGH )
    super.body();

    // 1. Configure Addressable Range (parent)
    // 2. Configure Address Space IDs (parent)
    `DV_CHECK_RANDOMIZE_FATAL(this)

    do_dma_op();            // 3. Run DMA operation
    poll_for_completion();  // 4. Check for completion

    `uvm_info( `gfn, "[DMA] Completing Smoke Sequence", UVM_HIGH)
  endtask: body
endclass
