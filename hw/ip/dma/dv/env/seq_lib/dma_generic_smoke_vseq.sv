// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*
  DMA 'generic' smoke test; runs smoke test with both 'memory-to-memory' and 'hardware handshaking'
  transfers.

    - FW allocates DMA enabled Memory Space for the data movement
    - FW configures Source Address and ASID
    - FW configures Destination Address and ASID
    - FW completes other configuration such as:
        i)    Operation Size
        ii)   Opcode
    - FW triggers the DMA operation
    - FW either
        i)    Poll for completion
        ii)   Waits for Completion Interrupt
    - Reset memory contents at the end of iteration
*/

class dma_generic_smoke_vseq extends dma_generic_vseq;
  `uvm_object_utils(dma_generic_smoke_vseq)
  `uvm_object_new

  // Limit the number of iterations and transactions to keep the smoke test fairly short.
  constraint iters_c {num_iters == 1;}
  constraint transactions_c {num_txns == 8;}

  // Permit only valid configurations for this simple smoke test
  virtual function bit pick_if_config_valid();
    return 1'b1;
  endfunction

  // Randomization of DMA configuration and transfer properties; here we are restricting the
  // permissible configuration and transfers to just very basic memory-to-memory copy operations.
  virtual function void randomize_item(ref dma_seq_item dma_config);
    // Allow only valid DMA configurations
    dma_config.valid_dma_config = 1;
    // Limit all parameters to 4B alignment, but leave 'handshake' open for randomization.
    `DV_CHECK_RANDOMIZE_WITH_FATAL(
      dma_config,
      src_addr[1:0] == dst_addr[1:0]; // Use same alignment for source and destination address
      total_data_size % 4 == 0; // Limit to multiples of 4B
      per_transfer_width == DmaXfer4BperTxn; // Limit to only 4B transfers
      opcode == OpcCopy;) // Avoid any involved operations such as SHA2 hashing
    `uvm_info(`gfn, $sformatf("DMA: Randomized a new transaction:%s",
                              dma_config.convert2string()), UVM_HIGH)
  endfunction

  // The functionality of this vseq is implemented in `dma_generic_vseq`
  virtual task body();
    `uvm_info(`gfn, "DMA: Starting generic smoke Sequence", UVM_LOW)
    super.body();
    `uvm_info(`gfn, "DMA: Completed generic smoke Sequence", UVM_LOW)
  endtask : body
endclass
