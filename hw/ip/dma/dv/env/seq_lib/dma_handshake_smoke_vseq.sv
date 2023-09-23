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
      clear_int_src == 0; // disable clearing of FIFO interrupt
      opcode == OpcCopy;)
    `uvm_info(`gfn, $sformatf("DMA: Randomized a new transaction\n %s",
                              dma_config.sprint()), UVM_HIGH)
  endfunction

  // Monitors busy bit in STATUS register
  task wait_for_idle();
    forever begin
      uvm_reg_data_t data;
      csr_rd(ral.status, data);
      if (!get_field_val(ral.status.busy, data)) begin
        `uvm_info(`gfn, "DMA in Idle state", UVM_MEDIUM)
        break;
      end
    end
  endtask

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
      `uvm_info(`gfn, $sformatf("handshake_value = 0x%0x", handshake_value), UVM_HIGH)
      start_device(dma_config);
      set_control_register(dma_config.opcode, // OPCODE
                           dma_config.handshake, // Handshake Enable
                           dma_config.auto_inc_buffer, // Auto-increment Buffer Address
                           dma_config.auto_inc_fifo, // Auto-increment FIFO Address
                           dma_config.direction, // Direction
                           1'b1); // Go
      set_hardware_handshake_intr(handshake_value);
      delay(5); // wait for DMA state change
      fork
        begin
          wait_for_idle();
        end
        begin
          // Wait for transmission of a number of bytes before releasing
          // hardware handshake interrupt
          uint num_bytes_per_txn = dma_config.transfer_width_to_num_bytes(
                                              dma_config.per_transfer_width);
          uint wait_bytes = $urandom_range(1, dma_config.total_transfer_size - num_bytes_per_txn);
          `uvm_info(`gfn, $sformatf("wait_bytes = %0d", wait_bytes), UVM_HIGH)
          wait_num_bytes_transfer(wait_bytes);
          `uvm_info(`gfn, $sformatf("Release hardware handshake interrupt"), UVM_HIGH)
          release_hardware_handshake_intr();
        end
      join
      delay(20); // wait to allow for transmission of last data
      // Clear GO bit
      `uvm_info(`gfn, "Clear GO bit", UVM_MEDIUM)
      ral.control.go.set(1'b0);
      csr_update(ral.control);
      // Clear DMA state
      clear();
      delay(10);
      // Stop dma_pull_seq
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
