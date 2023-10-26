// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Handshake mode smoke sequence
// testing the basic operation of DMA in hardware handshake mode
class dma_handshake_smoke_vseq extends dma_base_vseq;
  rand int num_txns;

  `uvm_object_utils(dma_handshake_smoke_vseq)
  `uvm_object_new

  constraint transactions_c {num_txns == valid_combinations.size();}

  // Function : Randomize dma_seq_item with valid and random asid combination
  function void randomize_item(ref dma_seq_item dma_config);
    int index = $urandom_range(0, valid_combinations.size() - 1);
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
      handshake == 1'b1; // Enable hardware handhake mode
      handshake_intr_en != 0; // At least one handshake interrupt signal must be enabled
      clear_int_src == 0;) // Disable clearing of FIFO interrupt
    `uvm_info(`gfn, $sformatf("DMA: Randomized a new transaction\n %s",
                              dma_config.sprint()), UVM_HIGH)
  endfunction

  virtual task body();
    logic [511:0] digest;

    `uvm_info(`gfn, "DMA: Starting handshake smoke Sequence", UVM_LOW)
    super.body();

    `uvm_info(`gfn, $sformatf("DMA: Running %d DMA Sequences", num_txns), UVM_LOW)

    for (int i = 0; i < num_txns; i++) begin
      bit stop = 1'b0;
      int status;

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
      `uvm_info(`gfn, $sformatf("handshake_value = 0x%0x", dma_config.lsio_trigger_i), UVM_HIGH)
      fork
        // Wait for completion of the entire transfer
        begin
          wait_for_completion(status);
          stop = 1'b1;
        end
        // Waggle the interrupt lines up and down at random times to keep the data moving
        begin
          uint bytes_to_move = dma_config.total_transfer_size;
          while (!stop) begin
            uint num_bytes_per_txn;
            uint bytes_moved;
            uint wait_bytes;

            set_hardware_handshake_intr(dma_config.lsio_trigger_i);

            // Wait for transmission of a number of bytes before releasing
            // hardware handshake interrupt
            num_bytes_per_txn = dma_config.transfer_width_to_num_bytes(
                                                dma_config.per_transfer_width);
            wait_bytes = $urandom_range(1, dma_config.chunk_data_size - num_bytes_per_txn);

            bytes_moved = get_bytes_written(dma_config);
            if (bytes_moved > bytes_to_move) begin
              `uvm_fatal(`gfn, $sformatf("Too many bytes moved = %0d, exceeds %0d", bytes_moved,
                         bytes_to_move))
            end
            if (wait_bytes > bytes_to_move - bytes_moved) begin
              wait_bytes = bytes_to_move - bytes_moved;
            end

            `uvm_info(`gfn, $sformatf("wait_bytes = %0d", wait_bytes), UVM_HIGH)

            // Delay until the chosen number of additional bytes have been transferred
            if (|wait_bytes) begin
              wait_num_bytes_transfer(bytes_moved + wait_bytes);
            end else begin
              // Processing still ongoing; parallel task `wait_for_completion` handles termination
              delay(1);
            end
            `uvm_info(`gfn, $sformatf("Release hardware handshake interrupt"), UVM_HIGH)
            release_hardware_handshake_intr();
          end
        end
      join

      poll_status();
      if (dma_config.opcode inside {OpcSha256, OpcSha384, OpcSha512}) begin
        read_sha2_digest(dma_config.opcode, digest);
      end

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

    `uvm_info(`gfn, "DMA: Completed Smoke Sequence", UVM_LOW)
  endtask : body
endclass
