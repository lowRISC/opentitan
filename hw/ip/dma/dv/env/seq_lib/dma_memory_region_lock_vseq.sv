// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence to test DMA enabled memory region lock
//
// Make sure DMA enabled memory region registers won't get updated once locked
// and can only be updated after reset
//
// 1. Configure DMA registers
// 2. [Lock] DMA enabled memory region registers
// If locked:
//  3. Write random data to DMA enabled memory region base and limit
//  4. Check if the value is updated
// 5. Start DMA operation
//  6. repeat 3 and 4
//  7. Wait for completion of operation
//  8. Repeat 3 and 4
// 9. Reset design
// 10. Check if DMA enabled memory region registers are unlocked
// 11. Repeat sequence for different combinations of Address space IDs
class dma_memory_region_lock_vseq extends dma_generic_vseq;

  `uvm_object_utils(dma_memory_region_lock_vseq)
  `uvm_object_new

  // Constrain number of iterations and transactions in each iteration; since registers should only
  // ever become unlocked after an iteration (as a result of block reset), aim for more iterations
  // and fewer transactions per iteration.
  constraint transactions_c {num_txns inside {[2:4]};}
  constraint num_iters_c {num_iters inside {[8:20]};}

  // Permit only valid configurations for this test
  //
  // Note: this means that the DMA-enabled memory range is known to be set up and marked as 'valid'
  //       for all transfers, but it does _not_ mean that the range will be locked.
  virtual function bit pick_if_config_valid();
    return 1'b1;
  endfunction

  bit operating;

  // Inter-task signaling
  event e_start;
  event e_stopped;

  // Captured reference values for the DMA-enabled memory range.
  logic [31:0] reference_range_valid;
  logic [31:0] reference_range_base;
  logic [31:0] reference_range_limit;

  // Check that memory region registers still match expectations, because they have been locked
  // to prevent changes.
  virtual task check_dma_memory_registers();
    uvm_reg_data_t data;
    mubi4_t lock_reg_value;

    `uvm_info(`gfn, "Checking DMA memory-enabled registers", UVM_MEDIUM)

    csr_rd(cfg.ral.range_regwen, data);
    lock_reg_value = mubi4_t'(get_field_val(ral.range_regwen.regwen, data));
    `DV_CHECK_EQ(lock_reg_value, MuBi4False,
                 $sformatf("REGWEN: 0x%0x is not locked as expected 0x%0x",
                           lock_reg_value, MuBi4False))

    csr_rd(ral.range_valid, data);
    `DV_CHECK_EQ(data, reference_range_valid,
                 $sformatf("DMA enabled memory range valid: 0x%0x doesn't match expected 0x%0x",
                           data, reference_range_valid))

    csr_rd(ral.enabled_memory_range_base, data);
    `DV_CHECK_EQ(data, reference_range_base,
                 $sformatf("DMA enabled memory region base: 0x%0x doesn't match expected 0x%0x",
                           data, reference_range_base))

    csr_rd(ral.enabled_memory_range_limit, data);
    `DV_CHECK_EQ(data, reference_range_limit,
                 $sformatf("DMA enabled memory region limit: 0x%0x doesn't match expected 0x%0x",
                           data, reference_range_limit))
  endtask

  // Randomize DMA enabled memory region registers
  virtual task randomize_dma_memory_registers();
    bit [3:0]  range_regwen;  // Randomize as bits rather than enum to test illegal values too.
    bit        dma_memory_valid;
    bit [31:0] dma_memory_base;
    bit [31:0] dma_memory_limit;
    `DV_CHECK_STD_RANDOMIZE_FATAL(range_regwen)
    `DV_CHECK_STD_RANDOMIZE_FATAL(dma_memory_valid)
    `DV_CHECK_STD_RANDOMIZE_FATAL(dma_memory_base)
    `DV_CHECK_STD_RANDOMIZE_FATAL(dma_memory_limit)

    `uvm_info(`gfn, $sformatf("Setting DMA-enabled base 0x%0x limit 0x%0x valid 0x%0x lock 0x%x",
              dma_memory_base, dma_memory_limit, dma_memory_valid, range_regwen), UVM_MEDIUM)

    set_dma_enabled_memory_range(.base(dma_memory_base),
                                 .limit(dma_memory_limit),
                                 .valid(dma_memory_valid),
                                 .lock(mubi4_t'(range_regwen)));
  endtask

  // Attempt to modify the registers, and check that they still hold the captured reference values.
  virtual task update_and_check_registers;
    randomize_dma_memory_registers();
    check_dma_memory_registers();
  endtask

  // Transaction is commencing
  virtual task starting_txn(int unsigned txn, int unsigned num_txns, ref dma_seq_item dma_config);
    mubi4_t range_regwen;
    bit [31:0] data;

    super.starting_txn(txn, num_txns, dma_config);

    // Has the DMA-enabled memory range been locked?
    //
    //   (If the range has not been locked, then attempting to change the memory base/limit shall
    //    be expected to induce test failures at present. It is permissible to change these values
    //    between transfers in order to support multiple FW/SW stages at boot.)
    csr_rd(cfg.ral.range_regwen, data);
    range_regwen = mubi4_t'(get_field_val(ral.range_regwen.regwen, data));
    if (range_regwen !== MuBi4True) begin
      // Capture the chosen state of the DMA-enabled memory range registers
      csr_rd(ral.range_valid,                reference_range_valid);
      csr_rd(ral.enabled_memory_range_base,  reference_range_base);
      csr_rd(ral.enabled_memory_range_limit, reference_range_limit);
      `DV_CHECK_EQ(reference_range_valid, 1'b1, "DMA enabled memory range not valid when expected")

      operating = 1'b1;
      // Signal to the parallel test task that the registers should be locked, and it should attempt
      // to modify the DMA-enabled memory range.
      ->e_start;
    end
  endtask

  // Transaction has ended
  virtual task ending_txn(int unsigned txn, int unsigned num_txns, ref dma_seq_item dma_config,
                          int status);
    if (operating) begin
      // Stop our parallel task
      operating = 1'b0;
      wait (e_stopped.triggered);

      // Transfer has ended, but the range register should still be locked...
      update_and_check_registers();
    end
  endtask

  virtual task body();
    `uvm_info(`gfn, "DMA: Starting dma_memory region lock Sequence", UVM_LOW)
    fork
      // Run smoke test body
      super.body();
      // Parallel task attempts to change the DMA-enabled memory range
      forever begin
        // Await a signal from the main task, indicating that the range should be locked.
        wait (e_start.triggered);
        while (operating) begin
          delay($urandom_range(10, 80));
          // Write random data into the DMA enabled memory region registers during the DMA
          // operation; these attempted writes should be suppressed by the 'regwen' locking within
          // the register interface.
          update_and_check_registers();
        end
        // Signal to the main task that we have stopped trying to modify the range.
        ->e_stopped;
      end
    join_any
    `uvm_info(`gfn, "DMA: Completed dma_memory region lock sequence", UVM_LOW)
  endtask : body
endclass
