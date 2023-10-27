// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*
  DMA 'memory-to-memory' smoke test
    - Generic operation through Mailbox initiated via FW
    - FW parses CMD object in Mailbox
    - FW sanitizes the said Object
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

class dma_memory_smoke_vseq extends dma_base_vseq;
  rand int num_txns;

  `uvm_object_utils(dma_memory_smoke_vseq)
  `uvm_object_new

  // Limit the number of transfers to keep the smoke test fairly short.
  constraint transactions_c {num_txns == 8;}

  // Randomization of DMA configuration and transfer properties
  virtual function void randomize_item(ref dma_seq_item dma_config);
    // Allow only valid DMA configurations
    dma_config.valid_dma_config = 1;
    // Limit all parameters to 4B alignment
    `DV_CHECK_RANDOMIZE_WITH_FATAL(
      dma_config,
      src_addr[1:0] == dst_addr[1:0]; // Use same alignment for source and destination address
      total_transfer_size % 4 == 0; // Limit to multiples of 4B
      per_transfer_width == DmaXfer4BperTxn; // Limit to only 4B transfers
      handshake == 1'b0;) //disable hardware handhake mode
    `uvm_info(`gfn, $sformatf("DMA: Randomized a new transaction:%s",
                              dma_config.convert2string()), UVM_HIGH)
  endfunction

  virtual task body();
    `uvm_info(`gfn, "DMA: Starting memory smoke Sequence", UVM_LOW)
    super.body();

    `uvm_info(`gfn, $sformatf("DMA: Running %d DMA Sequences", num_txns), UVM_LOW)

    for (int i = 0; i < num_txns; i++) begin
      `uvm_info(`gfn, $sformatf("DMA: Started Sequence #%0d", i), UVM_LOW)
      randomize_item(dma_config);
      run_common_config(dma_config);
      start_device(dma_config);
      set_control_register(dma_config.opcode, // OPCODE
                           1'b1,              // Initial transfer
                           dma_config.handshake, // Handshake Enable
                           dma_config.auto_inc_buffer, // Auto-increment Buffer Address
                           dma_config.auto_inc_fifo, // Auto-increment FIFO Address
                           dma_config.direction, // Direction
                           1'b1); // Go
      poll_status();
      clear();
      stop_device();
      apply_resets_concurrently();
      delay(10);
      // Reset config
      dma_config.reset_config();
      clear_memory();
      enable_interrupt();
      `uvm_info(`gfn, $sformatf("DMA: Completed Sequence #%d", i), UVM_LOW)
    end

    `uvm_info(`gfn, "DMA: Completed memory smoke Sequence", UVM_LOW)
  endtask : body
endclass
