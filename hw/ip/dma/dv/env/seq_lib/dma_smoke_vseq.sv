// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*
  DMA Smoke - Generic DMA Operation
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
*/

class dma_smoke_vseq extends dma_base_vseq;
  rand int num_txns;

  `uvm_object_utils(dma_smoke_vseq)
  `uvm_object_new

  // Constraint : Data and Transfer Size limit for Simulation-time reduction
  constraint dma_data_size_c {
    soft $countones(cfg_total_size) == 1; // Make it power of 2 for convenience
    soft cfg_transfer_size == 2'b11;
    soft cfg_total_size < 32'h100;
  }

  constraint transactions_c {
    num_txns >= 1;
    num_txns < 10;
  }

  virtual task body();
    `uvm_info(`gfn, "DMA: Starting Smoke Sequence", UVM_HIGH)
    super.body();

    `uvm_info(`gfn, $sformatf("DMA: Running %d DMA Sequences", num_txns + 1), UVM_HIGH)

    // First
    set_control_register();
    poll_status();
    `uvm_info(`gfn, "DMA: Completed Sequence #1", UVM_HIGH)

    // Subsequent
    for (int i = 0; i < num_txns; i++) begin
      clear();
      delay(10);
      randomize_new_address();
      set_source_address();
      set_destination_address_and_limit();
      set_address_space_id();
      `DV_CHECK_STD_RANDOMIZE_FATAL(cfg_direction)
      set_control_register();
      poll_status();
      `uvm_info(`gfn, $sformatf("DMA: Completed Sequence #%d", i + 2), UVM_HIGH)
    end

    `uvm_info(`gfn, "DMA: Completed Smoke Sequence", UVM_HIGH)
  endtask: body
endclass
