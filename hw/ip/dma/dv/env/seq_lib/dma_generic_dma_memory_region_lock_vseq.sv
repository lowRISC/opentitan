// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence to test DMA enabled memory region lock
//
// Make sure DMA enabled memory region registers won't get updated once locked
// and can only be updated after reset
//
// 1. Configure DMA registers
// 2. Lock DMA enabled memory region registers
// 3. Write random data to DMA enabled memory region base and limit
// 4. Check if the value is updated
// 5. Start DMA operation
// 6. repeat 3 and 4
// 7. Wait for completion of operation
// 8. Repeat 3 and 4
// 9. Reset design
// 10. Check if DMA enabled memory region registers are unlocked
// 11. Repeat sequence for different combinations of Address space IDs
class dma_generic_dma_memory_region_lock_vseq extends dma_generic_smoke_vseq;

  `uvm_object_utils(dma_generic_dma_memory_region_lock_vseq)
  `uvm_object_new

  // Check that memory region registers are locked
  virtual task check_dma_memory_registers(ref dma_seq_item dma_config);
    uvm_reg_data_t data;
    mubi4_t lock_reg_value;
    csr_rd(ral.enabled_memory_range_base, data);
    `DV_CHECK_EQ(dma_config.mem_range_base, data,
                 $sformatf("DMA enabled memory region base: 0x%0x register doesnt match: 0x%0x",
                           data, dma_config.mem_range_base))
    csr_rd(ral.enabled_memory_range_limit, data);
    `DV_CHECK_EQ(dma_config.mem_range_limit, data,
                 $sformatf("DMA enabled memory region limit: 0x%0x doesnt match: 0x%0x",
                 data, dma_config.mem_range_limit))
    csr_rd(cfg.ral.range_regwen, data);
    lock_reg_value = mubi4_t'(get_field_val(ral.range_regwen.regwen, data));
    `DV_CHECK_EQ(lock_reg_value, MuBi4False)
  endtask

  // Randomize DMA enabled memory region registers
  virtual task randomize_dma_memory_registers();
    bit [31:0] dma_memory_base;
    bit [31:0] dma_memory_limit;
    `DV_CHECK_STD_RANDOMIZE_FATAL(dma_memory_base)
    `DV_CHECK_STD_RANDOMIZE_FATAL(dma_memory_limit)
    set_dma_enabled_memory_range(.base(dma_memory_base),
                                 .limit(dma_memory_limit),
                                 .lock(MuBi4True));
 endtask

 virtual task update_and_check_register(ref dma_seq_item dma_config);
  randomize_dma_memory_registers();
  check_dma_memory_registers(dma_config);
 endtask

 virtual task body();
    `uvm_info(`gfn, "DMA: Starting dma_memory region lock Sequence", UVM_LOW)
    init_model();
    enable_interrupt();
    // Disable CSR assert
    set_csr_assert_en(0);
    for (int i = 0; i < num_txns; i++) begin
      `uvm_info(`gfn, $sformatf("DMA: Started Sequence #%0d", i), UVM_LOW)
      randomize_item(dma_config, i);
      run_common_config(dma_config);
      start_device(dma_config);
      // Write random data in to DMA enabled memory region registers
      // before DMA operation
      repeat(5) begin
        update_and_check_register(dma_config);
      end
      set_control_register(dma_config.opcode, // OPCODE
                           1'b1,              // Initial transfer
                           dma_config.handshake, // Handshake Enable
                           dma_config.auto_inc_buffer, // Auto-increment Buffer Address
                           dma_config.auto_inc_fifo, // Auto-increment FIFO Address
                           dma_config.direction, // Direction
                           1'b1); // Go
      // Write random data in to DMA enabled memory region registers
      // during DMA operation
      fork
        poll_status();
        // DMA enabled memory region registers can only be unlocked with design reset.
        // So, this check will also work if the DMA operation completes early.
        repeat(5) begin
          update_and_check_register(dma_config);
        end
      join
      // Clear DMA state
      clear();
      delay(10);
      update_and_check_register(dma_config);
      stop_device();
      apply_resets_concurrently();
      delay(10);
      // Reset config
      dma_config.reset_config();
      clear_memory();
      enable_interrupt();
      `uvm_info(`gfn, $sformatf("DMA: Completed Sequence #%d", i), UVM_LOW)
    end

    `uvm_info(`gfn, "DMA: Completed dma_memory region lock sequence", UVM_LOW)
  endtask : body

endclass: dma_generic_dma_memory_region_lock_vseq
