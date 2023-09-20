// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Handshake mode smoke sequence
// testing the basic operation of DMA in hardware handshake mode
class dma_handshake_smoke_vseq extends dma_base_vseq;
  rand int num_txns;

  `uvm_object_utils(dma_handshake_smoke_vseq)
  `uvm_object_new

  // Handshake interrupt value
  rand bit [dma_reg_pkg::NumIntClearSources-1:0] handshake_value;

  constraint transactions_c {num_txns == valid_combinations.size();}

  // Function : Randomise dma_seq_item with valid and random asid combination
  function void randomise_item(ref dma_seq_item dma_config);
    int num_valid_combinations = valid_combinations.size();
    int index = $urandom_range(0, num_valid_combinations - 1);
    addr_space_id_t valid_combination = valid_combinations[index];
    // Allow only valid DMA configurations
    dma_config.valid_dma_config = 1;
    // Limit all parameters to 4B alignment
    `DV_CHECK_RANDOMIZE_WITH_FATAL(
      dma_config,
      src_asid == valid_combination.src_id;
      dst_asid == valid_combination.dst_id;
      src_addr[1:0] == dst_addr[1:0]; // Use same alignment for source and destination address
      total_transfer_size % 4 == 0; // Limit to multiples of 4B
      per_transfer_width == DmaXfer4BperTxn; // Limit to only 4B transfers
      handshake == 1'b1; //disable hardware handhake mode
      handshake_intr_en != 0; // At least one handshake interrupt signal must be enabled
      opcode == OpcCopy;)
    `uvm_info(`gfn, $sformatf("DMA: Randomized a new transaction\n %s",
                              dma_config.sprint()), UVM_HIGH)
  endfunction

  virtual task body();
    `uvm_info(`gfn, "DMA: Starting handshake smoke Sequence", UVM_LOW)
    super.body();

    `uvm_info(`gfn, $sformatf("DMA: Running %d DMA Sequences", num_txns), UVM_LOW)

    for (int i = 0; i < num_txns; i++) begin
      `uvm_info(`gfn, $sformatf("DMA: Started Sequence #%0d", i), UVM_LOW)
      randomise_item(dma_config);
      run_common_config(dma_config);
      // Toggle random bit in hardware handshake input interrupt
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(handshake_value,
                                         handshake_value &
                                         dma_config.handshake_intr_en != 0;)
      start_device(dma_config);
      set_control_register(dma_config.opcode, // OPCODE
                           dma_config.handshake, // Handshake Enable
                           dma_config.auto_inc_buffer, // Auto-increment Buffer Address
                           dma_config.auto_inc_fifo, // Auto-increment FIFO Address
                           dma_config.direction, // Direction
                           1'b1); // Go
      set_hardware_handshake_intr(handshake_value);
      poll_status();
      release_hardware_handshake_intr();
      clear();
      delay(10);
      stop_device();
      delay(10);
      apply_resets_concurrently();
      delay(10);
      // Reset config
      dma_config.reset_config();
      clear_memory();
      enable_interrupt();
      `uvm_info(`gfn, $sformatf("DMA: Completed Sequence #%d", i), UVM_LOW)
    end

    `uvm_info(`gfn, "DMA: Completed Smoke Sequence", UVM_LOW)
  endtask : body
endclass
