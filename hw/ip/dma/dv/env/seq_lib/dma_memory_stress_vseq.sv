// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Stress 'memory-to-memory' DMA transfers
class dma_memory_stress_vseq extends dma_base_vseq;
  rand int num_txns;

  `uvm_object_utils(dma_memory_stress_vseq)
  `uvm_object_new

  rand uint num_iter; // Number of configurations of DMA

  // Constrain number of iterations and transactions in each iteration
  constraint transactions_c {num_txns inside {[10:40]};}
  constraint num_iter_c {num_iter inside {[5:20]};}

  function bit pick_if_config_valid();
    bit valid_config;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(valid_config, valid_config dist { 0:= 20, 1 := 80};)
    return valid_config;
  endfunction

  function void randomize_config(ref dma_seq_item dma_config);
    dma_config.valid_dma_config = pick_if_config_valid();
    if (dma_config.valid_dma_config) begin
      // Allow only valid DMA configurations
      `uvm_info(`gfn, " ***** Choosing a valid DMA configuration *****", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_WITH_FATAL(dma_config, handshake == 0;)
      `DV_CHECK(dma_config.is_valid_config);
    end else begin
      `uvm_info(`gfn, "***** Choosing a possibly invalid DMA configuration *****", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_WITH_FATAL(dma_config, handshake == 0;)
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

    // We have just reset the device, so we may now try randomizing these until such time as we
    // choose to lock the memory range.
    set_asid_buf_limit_randomization(dma_config, 1);
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

  // Enable/disable randomization of ASID
  // so that source and destination interfaces remain same address and other parameters get randomized
  function void set_asid_buf_limit_randomization(ref dma_seq_item dma_config, input bit enable);
    string action = enable ? "Enabled" : "Disabled";
    dma_config.src_asid.rand_mode(enable);
    dma_config.dst_asid.rand_mode(enable);
    dma_config.asid_c.constraint_mode(enable);
    `uvm_info(`gfn, $sformatf("%s ASID randomization", action), UVM_HIGH)
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
      ral.status.error.set(1'b0);
      ral.status.error_code.set(0);
      csr_update(ral.status);
    end
  endtask

  virtual task body();
    `uvm_info(`gfn, "DMA: Starting memory stress Sequence", UVM_LOW)
    init_model();
    enable_interrupt();
    for (uint i = 0; i < num_iter; i++) begin
      `uvm_info(`gfn, $sformatf("Running iteration %0d/%0d of DMA stress", i, num_iter), UVM_LOW)
      randomize_iter_config(dma_config);
      // For each ASID and mem buffer configuration randomize other DMA parameters
      for (uint j = 0; j < num_txns; j++) begin
        `uvm_info(`gfn, $sformatf("Running transaction %0d/%0d of DMA stress", j, num_txns),
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
        poll_status();
        stop_device();
        clear_errors(dma_config);
        // We need to clear the outputs, especially `status.done`
        clear();
        randomize_txn_config(dma_config);
      end
      apply_resets_concurrently();
      delay(10);
      // Reset config
      dma_config.reset_config();
      clear_memory();
      enable_interrupt();
    end
    `uvm_info(`gfn, "DMA: Completed memory stress Sequence", UVM_LOW)
  endtask : body
endclass
