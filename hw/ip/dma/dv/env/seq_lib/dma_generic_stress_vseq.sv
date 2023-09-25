// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Stress Generic mode of DMA Operation
class dma_generic_stress_vseq extends dma_generic_smoke_vseq;
  rand int num_txns;

  `uvm_object_utils(dma_generic_stress_vseq)
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

  // Function : Rerandomization of address ranges
  function void randomize_iter_config(ref dma_seq_item dma_config);
    enable_asid_buf_limit_randomization(dma_config);
    if (pick_if_config_valid()) begin
      `uvm_info(`gfn, "Using a valid DMA configuration", UVM_MEDIUM)
      super.randomize_item(dma_config);
      // Reset constrain control bits after randomization
      dma_config.valid_dma_config = 0;
      dma_config.align_address = 0;
    end else begin
      `DV_CHECK_RANDOMIZE_WITH_FATAL(dma_config, handshake == 0; opcode == OpcCopy;)
    end
    `uvm_info(`gfn, $sformatf("Randomized DMA iter configuration\n%s", dma_config.sprint()),
              UVM_HIGH)
    disable_asid_buf_limit_randomization(dma_config);
  endfunction

  // Randomizes transaction configuration of each iteration
  function void randomize_txn_config(ref dma_seq_item dma_config);
    dma_config.valid_dma_config = pick_if_config_valid();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(dma_config, handshake == 0;)
    // Reset constraint control bits after randomization
    dma_config.valid_dma_config = 0;
    `uvm_info(`gfn, $sformatf("Randomized DMA txn configuration\n%s", dma_config.sprint()),
              UVM_HIGH)
  endfunction

  // Disable randomization of ASID
  // so that source and destination interfraces remain same address and other parameters get randomized
  function void disable_asid_buf_limit_randomization(ref dma_seq_item dma_config);
    dma_config.src_asid.rand_mode(0);
    dma_config.dst_asid.rand_mode(0);
    dma_config.asid_c.constraint_mode(0);
    `uvm_info(`gfn, "Disabled ASID and DMA enabled memory buffer randomization", UVM_HIGH)
  endfunction

  function void enable_asid_buf_limit_randomization(ref dma_seq_item dma_config);
    dma_config.src_asid.rand_mode(1);
    dma_config.dst_asid.rand_mode(1);
    dma_config.asid_c.constraint_mode(1);
    `uvm_info(`gfn, "Enabled ASID and DMA enabled memory buffer randomization", UVM_HIGH)
  endfunction

  task clear_errors(ref dma_seq_item dma_config);
    uvm_reg_data_t status;
    csr_rd(ral.status, status);
    if (get_field_val(ral.status.error, status)) begin
      `DV_CHECK(!dma_config.check_config())
      `uvm_info(`gfn, "Clear GO bit", UVM_MEDIUM)
      ral.control.go.set(1'b0);
      csr_update(ral.control);
      `uvm_info(`gfn, "Clear error status", UVM_MEDIUM)
      ral.status.error.set(1'b0);
      ral.status.error_code.set(0);
      csr_update(ral.status);
      // Clear DMA state and GO bit only in case of error
      clear();
    end
  endtask

  virtual task body();
    `uvm_info(`gfn, "DMA: Starting generic stress Sequence", UVM_LOW)
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
                             dma_config.handshake, // Handshake Enable
                             dma_config.auto_inc_buffer, // Auto-increment Buffer Address
                             dma_config.auto_inc_fifo, // Auto-increment FIFO Address
                             dma_config.direction, // Direction
                             1'b1); // Go
        poll_status();
        stop_device();
        clear_errors(dma_config);
        // Randomize DMA config except ASID and mem buffer registers
        randomize_txn_config(dma_config);
      end
      apply_resets_concurrently();
      delay(10);
      // Reset config
      dma_config.reset_config();
      clear_memory();
      enable_interrupt();
    end
    `uvm_info(`gfn, "DMA: Completed generic stress Sequence", UVM_LOW)
  endtask : body
endclass
