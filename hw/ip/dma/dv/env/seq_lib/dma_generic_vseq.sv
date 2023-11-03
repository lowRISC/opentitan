// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Generic DMA transfer sequence
class dma_generic_vseq extends dma_base_vseq;
  `uvm_object_utils(dma_generic_vseq)
  `uvm_object_new

  // Number of iterations, with DMA controller being reset after each iteration.
  rand uint num_iters;
  // Number of transactions per iteration.
  rand uint num_txns;

  virtual function bit pick_if_config_valid();
    bit valid_config;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(valid_config, valid_config dist { 0 := 20, 1 := 80};)
    return valid_config;
  endfunction

  // Randomization of DMA configuration and transfer properties
  virtual function void randomize_config(ref dma_seq_item dma_config);
    dma_config.valid_dma_config = pick_if_config_valid();
    if (dma_config.valid_dma_config) begin
      // Allow only valid DMA configurations
      `uvm_info(`gfn, " ***** Choosing a valid DMA configuration *****", UVM_MEDIUM)
      randomize_item(dma_config);
      `DV_CHECK(dma_config.is_valid_config);
    end else begin
      `uvm_info(`gfn, "***** Choosing a possibly invalid DMA configuration *****", UVM_MEDIUM)
      randomize_item(dma_config);
    end
    // Has the DMA-enabled memory configuration now been locked?
    if (dma_config.mem_range_lock != MuBi4True) begin
      // Suppress further attempts at randomization because otherwise the TB will form incorrect
      // predictions.
      set_memory_range_randomization(dma_config, 0);
    end

    // Reset constraint control bits after randomization
    dma_config.valid_dma_config = 0;
  endfunction

  // Function : Re-randomization of address ranges
  function void randomize_iter_config(ref dma_seq_item dma_config);
    // We have just reset the device, so we may now try randomizing the memory range until such
    // time as we choose to lock it.
    set_memory_range_randomization(dma_config, 1);

    randomize_config(dma_config);

    `uvm_info(`gfn, $sformatf("Randomized DMA iter configuration\n%s", dma_config.sprint()),
              UVM_HIGH)
  endfunction

  // Randomizes transaction configuration of each iteration
  function void randomize_txn_config(ref dma_seq_item dma_config);
    randomize_config(dma_config);

    `uvm_info(`gfn, $sformatf("Randomized DMA txn configuration\n%s", dma_config.sprint()),
              UVM_HIGH)
  endfunction

  // Once we have settled upon a valid configuration that moves data between the OT and SoC
  // domains we must prevent further randomization of the base/limit registers, because otherwise
  // the TB will form incorrect predictions.
  function void set_memory_range_randomization(ref dma_seq_item dma_config, input bit enable);
    string action = enable ? "Enabled" : "Disabled";
    dma_config.mem_range_valid.rand_mode(enable);
    dma_config.mem_range_base.rand_mode(enable);
    dma_config.mem_range_limit.rand_mode(enable);
    dma_config.mem_range_limit_c.constraint_mode(enable);
    `uvm_info(`gfn, $sformatf("%s DMA-enabled memory range randomization", action), UVM_HIGH)
  endfunction

  task clear_errors(ref dma_seq_item dma_config);
    uvm_reg_data_t status;
    csr_rd(ral.status, status);
    if (get_field_val(ral.status.error, status)) begin
      // TODO: There are other causes of errors in more complex tests
      bit valid = dma_config.check_config("clear_errors");
      `DV_CHECK(!valid);
      ral.control.go.set(1'b0);
      csr_update(ral.control);
      `uvm_info(`gfn, "Clear error status", UVM_MEDIUM)
      ral.status.error.set(1'b1);
      csr_update(ral.status);
    end
  endtask

  virtual task body();
    super.body();

    for (uint i = 0; i < num_iters; i++) begin
      enable_interrupt();

      `uvm_info(`gfn, $sformatf("DMA: Running iteration %0d/%0d", i + 1, num_iters), UVM_LOW)
      randomize_iter_config(dma_config);

      // TODO: can/shall we re-randomize the transaction count on each iteration?
      for (uint j = 0; j < num_txns; j++) begin
        bit [31:0] num_bytes_supplied;
        logic [511:0] digest;
        bit stop = 1'b0;
        int status;

        `uvm_info(`gfn, $sformatf("DMA: Running transaction %0d/%0d", j + 1, num_txns),
                  UVM_LOW)

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

        // Keep track of the number of bytes that we've supplied to the DMA controller
        num_bytes_supplied = dma_config.chunk_size(0);

        fork
          // Wait for completion of the entire transfer
          // - all chunks have been completed and Done interrupt/Status bit detected
          // - error has occurred (eg. configuration rejected, TL-UL error response)
          // - aborted, in response to abort request
          // - timeout
          while (!stop) begin
            wait_for_completion(status);
            if (status) begin
              stop = 1'b1;
            end else begin
              // 'Done' but perhaps not yet finished
              bit [31:0] num_written = get_bytes_written(dma_config);
              `uvm_info(`gfn,
                        $sformatf("STATUS.done bit set after 0x%0x bytes of 0x%0x-byte transfer",
                        num_written, dma_config.total_transfer_size), UVM_MEDIUM)
              // Has the entire transfer been completed yet?
              if (num_written >= dma_config.total_transfer_size) begin
                stop = 1'b1;
              end else if (!dma_config.handshake) begin
                // Model the FirmWare running on the OT side, responding to the Done interrupt and
                // nudging the controller to perform the next chunk of a multi-chunk transfer

                // TODO: clear the Done bit; PR #660 is aimed at obviating this
                ral.status.done.set(1'b1);
                csr_update(ral.status);

                // Supply the next chunk of input data
                void'(configure_mem_model(dma_config, num_bytes_supplied));
                num_bytes_supplied += dma_config.chunk_size(num_bytes_supplied);

                // Nudge the DMA controller to start processing the next chunk of data
                ral.control.initial_transfer.set(1'b0);
                ral.control.go.set(1'b1);
                csr_update(ral.control);
              end else begin
                `uvm_fatal(`gfn,
                      $sformatf("STATUS.done bit set prematurely (0x%x byte(s) of 0x%x transferred",
                      num_written, dma_config.total_transfer_size))
              end
            end
          end
          begin
            // In handshaking mode there is no reporting of chunk completion, only that the entire
            // transfer has completed, so we must monitor the bus read/traffic and rely upon the
            // 'bytes read' and 'bytes written' counters to supply input and check output at the
            // appropriate times.
            while (dma_config.handshake && !stop &&
                   num_bytes_supplied < dma_config.total_transfer_size) begin
              if (num_bytes_supplied <= get_bytes_read(dma_config)) begin
                // All supplied input data has been read; provide the next complete chunk of data
                // in zero simulation time.
                uint chunk_size = dma_config.chunk_size(num_bytes_supplied);
                supply_data(dma_config, num_bytes_supplied, chunk_size);
                num_bytes_supplied += chunk_size;
              end
              delay(1);
            end
          end
          // Waggle the interrupt lines up and down at random times to keep the data moving
          begin
            uint bytes_to_move = dma_config.total_transfer_size;
            while (dma_config.handshake && !stop) begin
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
                wait_num_bytes_transfer(bytes_moved + wait_bytes, stop);
              end else begin
                // Processing still ongoing; parallel task `wait_for_completion` handles termination
                delay(1);
              end
              `uvm_info(`gfn, $sformatf("Release hardware handshake interrupt"), UVM_HIGH)
              release_hardware_handshake_intr();
            end
          end
        join

        if (dma_config.opcode inside {OpcSha256, OpcSha384, OpcSha512}) begin
          read_sha2_digest(dma_config.opcode, digest);
        end

        clear_errors(dma_config);
        // We need to clear the outputs, especially `status.done`
        clear();

        // Now that we've finished all DUT accesses for his iteration...
        stop_device();

        // Set up randomized configuration for the next transaction
        randomize_txn_config(dma_config);
      end
      apply_resets_concurrently();
      delay(10);
      // Reset config
      dma_config.reset_config();
      clear_memory();
    end
  endtask : body
endclass
