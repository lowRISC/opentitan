// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: pending checks
// - handshake interrupt check
// - Alert checks
class dma_scoreboard extends cip_base_scoreboard #(
  .CFG_T(dma_env_cfg),
  .RAL_T(dma_reg_block),
  .COV_T(dma_env_cov)
);
  `uvm_component_utils(dma_scoreboard)

  `uvm_component_new

  // Queue structures holding the expected requests on selected source and destination interfaces
  tl_seq_item src_queue[$];  // Request and response items on source TL interface
  tl_seq_item dst_queue[$];  // Request and response items on destination TL interface

  bit [63:0] exp_src_addr;   // Expected address for next source request
  bit [63:0] exp_dst_addr;   // Expected address for next destination request

  // Internal copy of the DMA configuration information for use in validating TL-UL transactions
  // This copy is updated in the `process_reg_write` function below
  dma_seq_item dma_config;

  // Indicates if DMA operation is in progress
  bit operation_in_progress;
  // Indicates if current DMA operation is valid or invalid
  bit current_operation_valid = 1;
  // Tracks the number of bytes read from the source
  uint num_bytes_read;
  // Expectation of how many bytes shall be transferred by the DMA controller before reporting Done
  // (for handshake mode this is the entire transfer, but for memory-to-memory operation it tracks
  //  the total size in bytes of the chunks thus far supplied).
  uint exp_bytes_transferred;
  // Variable to keep track of number of bytes transferred in current operation
  uint num_bytes_transferred;
  // Tracks the number of destination bytes checked against the source
  uint num_bytes_checked;
  // Variable to indicate if TL error is detected on interface
  bit src_tl_error_detected;
  bit dst_tl_error_detected;
  // Bit to indicate if DMA operation is explicitly aborted with register write
  bit abort_via_reg_write;

  // Interrupt enable state
  bit intr_enable_done;
  bit intr_enable_error;
  bit intr_enable_mem_limit;

  // bit to indicate if dma_memory_buffer_limit interrupt is reached
  bit exp_buffer_limit_intr;
  // Bit to indicate if dma_error interrupt is asserted
  bit exp_dma_err_intr;
  // bit to indicate if dma_done interrupt is asserted
  bit exp_dma_done_intr;
  // True if in hardware handshake mode and the FIFO interrupt has been cleared
  bit fifo_intr_cleared;
  // Variable to indicate number of writes expected to clear FIFO interrupts
  uint num_fifo_reg_write;
  // Variable to store clear_int_src register intended for use in monitor_lsio_trigger task
  // since ref argument can not be used in fork-join_none
  bit[31:0] clear_int_src;
  bit [TL_DW-1:0] exp_digest[16];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Create a_channel analysis fifo
    foreach (cfg.dma_a_fifo[key]) begin
      tl_a_chan_fifos[cfg.dma_a_fifo[key]] = new(cfg.dma_a_fifo[key], this);
    end
    foreach (cfg.dma_d_fifo[key]) begin
      tl_d_chan_fifos[cfg.dma_d_fifo[key]] = new(cfg.dma_d_fifo[key], this);
    end
    foreach (cfg.dma_dir_fifo[key]) begin
      tl_dir_fifos[cfg.dma_dir_fifo[key]] = new(cfg.dma_dir_fifo[key], this);
    end
    // `dma_config` serves to hold a copy of the DMA configuration registers, which are the same
    // values being randomized and used by the vseqs. Its fields are updated in `process_reg_write`
    // and randomizing may catch failures to update them properly
    dma_config = dma_seq_item::type_id::create("dma_config");
    if (!dma_config.randomize()) begin
      `uvm_fatal(`gfn, "Failed to randomize dma_config")
    end
  endfunction : build_phase

  // Look up the given address in the list of 'Clear Interrupt' addresses, returning a positive
  // index iff found.
  function int int_addr_lookup(bit [31:0] addr);
    for (uint idx = 0; idx < dma_config.int_src_addr.size(); idx++) begin
      if (dma_config.int_src_addr[idx] == addr) begin
        // Address matches; this address should just receive write traffic.
        return int'(idx);
      end
    end
    return -1;
  endfunction : int_addr_lookup

  // Check if the address matches our expectations and is valid for the current configuration.
  // This method is common for both source and destination address.
  function void check_addr(bit [63:0]       addr,        // Observed address.
                           bit [63:0]       exp_addr,    // Expectation.
                           bit              restricted,  // DMA-enabled range applies.
                           bit              fixed_addr,  // Fixed address (FIFO w/out auto-inc).
                           // Expected address range for this accesses of this type.
                           bit [63:0]       range_start,
                           bit [31:0]       range_len,
                           // Configuration for this transfer.
                           ref dma_seq_item dma_config,
                           input string     check_type);  // Type of access.
    // End of valid address range; dependent upon the chunk/transfer size and auto-inc setting.
    bit [63:0] range_end = range_start + range_len;
    int idx;

    `uvm_info(`gfn, $sformatf("%s access to 0x%0x, exp 0x%0x, fixed_addr %d, restricted %d",
                              check_type, addr, exp_addr, fixed_addr, restricted), UVM_DEBUG)
    `uvm_info(`gfn,
              $sformatf("  (%s range is [0x%0x,0x%0x) and DMA-enabled range is [0x%0x,0x%0x))",
                        check_type, range_start, range_end,
                        dma_config.mem_range_base, dma_config.mem_range_limit), UVM_DEBUG)

    `DV_CHECK(addr[1:0] == 0, $sformatf("Address is not 4 Byte aligned"))

    // Is this end of the transfer a fixed address?
    // (FIFO end of a transfer in hardware handshaking mode, without address auto-incrementing.)
    if (fixed_addr) begin
      `DV_CHECK(addr[63:2] == range_start[63:2],
                $sformatf("0x%0x doesn't match %s start addr:0x%0x (handshake mode no auto-incr)",
                          addr, check_type, range_start))
    end else begin
      // Addresses generated by DMA are 4-Byte aligned (refer #338)
      bit [63:0] aligned_start_addr = {range_start[63:2], 2'b00};
      // Generic mode address check
      `DV_CHECK(addr >= aligned_start_addr && addr < range_end,
                $sformatf("0x%0x not in %s addr range [0x%0x,0x%0x)", addr, check_type,
                          aligned_start_addr, range_end))

      // Check that this address lies within the DMA-enabled memory range, where applicable.
      if (restricted) begin
        `DV_CHECK(addr >= dma_config.mem_range_base && addr < dma_config.mem_range_limit,
                  $sformatf("%s addr 0x%0x does not lie within the DMA-enabled range [0x%0x,0x%0x)",
                            check_type, addr, dma_config.mem_range_base,
                            dma_config.mem_range_limit))
      end
    end

    // Is this request to the address we expected?
    `DV_CHECK(addr[63:2] == exp_addr[63:2],
              $sformatf("%s access 0x%0x does not match expectation 0x%0x", check_type,
                        addr, exp_addr))
  endfunction

  // On-the-fly checking of write data against the pre-randomized source data
  function void check_write_data(string if_name, ref tl_seq_item item);
    bit [tl_agent_pkg::DataWidth-1:0] wdata = item.a_data;
    bit [31:0] offset = num_bytes_transferred;

    `uvm_info(`gfn, $sformatf("if_name %s: write addr 0x%0x mask 0x%0x data 0x%0x", if_name,
                              item.a_addr, item.a_mask, item.a_data), UVM_HIGH)

    // Check each of the bytes being written, Little Endian byte ordering
    for (int i = 0; i < $bits(item.a_mask); i++) begin
      if (item.a_mask[i]) begin
        `uvm_info(`gfn, $sformatf("src_data %0x write data 0x%0x",
                                  cfg.src_data[offset], wdata[7:0]), UVM_DEBUG)
        `DV_CHECK_EQ(cfg.src_data[offset], wdata[7:0])
        offset++;
      end
      wdata = wdata >> 8;
    end
  endfunction

  // Predict the address to which the next access of this type should occur.
  function bit [63:0] predict_addr(bit [63:0]       addr,
                                   // Bytes read/written, after the current bus access.
                                   uint             num_bytes,
                                   // Start address of transfer (= start of first chunk).
                                   bit [63:0]       start_addr,
                                   bit              fifo_access,
                                   // Configuration for this transfer.
                                   ref dma_seq_item dma_config,
                                   input string     check_type);  // Type of access.
    // Default is to advance by the transfer amount from our previous prediction.
    bit [63:0] next_addr = addr + dma_config.txn_bytes();

    // Are we expecting another access?
    if (num_bytes < dma_config.total_transfer_size) begin
      if (!dma_config.chunk_data_size || (num_bytes % dma_config.chunk_data_size)) begin
        // Still within this chunk; do we advance per bus transaction?
        if (fifo_access && !dma_config.auto_inc_fifo) begin
          // Fixed address.
          next_addr = addr;
        end
      end else if (fifo_access || !dma_config.auto_inc_buffer) begin
        // End of a chunk, but all chunks overlap.
        next_addr = start_addr;
      end
    end else begin
      next_addr = {64{1'b1}};  // Invalid; induce a mismatch if there is another access.
    end

    `uvm_info(`gfn, $sformatf("%s prediction 0x%0x (num_bytes 0x%0x after 0x%0x)",
                              check_type, next_addr, num_bytes, addr), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("  (start 0x%0x, fifo %d, inc_fifo %d, inc_buffer %d)",
                              start_addr, fifo_access, dma_config.auto_inc_fifo,
                              dma_config.auto_inc_buffer), UVM_DEBUG)
    return next_addr;
  endfunction

  // Process items on Addr channel
  task process_tl_addr_txn(string if_name, ref tl_seq_item item);
    uint expected_txn_size = dma_config.transfer_width_to_a_size(
                               dma_config.per_transfer_width);
    uint expected_per_txn_bytes = dma_config.transfer_width_to_num_bytes(
                                    dma_config.per_transfer_width);
    tl_a_op_e a_opcode = tl_a_op_e'(item.a_opcode);
    bit [31:0] memory_range;
    int int_source;

    `uvm_info(`gfn, $sformatf("Got addr txn \n:%s", item.sprint()), UVM_DEBUG)
    // Common checks
    // Check if the transaction is of correct size
    `DV_CHECK_EQ(item.a_size, 2); // Always 4B

    // The range of memory addresses that should be touched by the DMA controller depends upon
    // whether the memory_buffer_inc is set in hardware handshake mode
    memory_range = dma_config.total_transfer_size;
    if (dma_config.handshake && !dma_config.auto_inc_buffer) begin
      // All chunks within the transfer overlap each other in memory
      memory_range = dma_config.chunk_data_size;
    end

    // Interface specific checks
    // - Read transactions are from Source interface and
    // - Write transactions are to destination interface
    if (!item.is_write()) begin // read transaction
      // Does the DMA-enabled memory range apply to this type of access?
      bit restricted = dma_config.mem_range_valid && (dma_config.src_asid == OtInternalAddr &&
                                                      dma_config.dst_asid != OtInternalAddr);

      // Check if the transaction has correct mask
      `DV_CHECK_EQ($countones(item.a_mask), 4) // Always 4B
      // Check source ASID for read transaction
      `DV_CHECK_EQ(if_name, cfg.asid_names[dma_config.src_asid],
                   $sformatf("Unexpected read txn on %s interface with source ASID %s",
                             if_name, dma_config.src_asid.name()))
      // Check if opcode is as expected
      `DV_CHECK(a_opcode inside {Get},
               $sformatf("Unexpected opcode : %d on %s", a_opcode.name(), if_name))

      // Is this address a 'Clear Interrupt' operation?
      int_source = int_addr_lookup(item.a_addr);
      `DV_CHECK_EQ(int_source, -1, "Unexpected Read access to Clear Interrupt address")

      // Validate the read address for this source access.
      check_addr(item.a_addr, exp_src_addr, restricted, dma_config.get_read_fifo_en(),
                 dma_config.src_addr, memory_range, dma_config, "Source");

      // Push addr item to source queue
      src_queue.push_back(item);
      `uvm_info(`gfn, $sformatf("Addr channel checks done for source item"), UVM_HIGH)

      // Update the count of bytes read from the source.
      // Note that this is complicated by the fact that the TL-UL host adapter always fetches
      // complete bus words, so we have to rely upon knowledge of the configured transfer amount.
      num_bytes_read += dma_config.txn_bytes();

      // Update expectation of next source access, predicting from our current expectation;
      // this is important because the current transaction address is missing its LSBs and thus
      // cannot be used.
      exp_src_addr = predict_addr(exp_src_addr, num_bytes_read, dma_config.src_addr,
                                  dma_config.handshake & (dma_config.direction == DmaRcvData),
                                  dma_config, "Source");
    end else begin // Write transaction
      // Does the DMA-enabled memory range apply to this type of access?
      bit restricted = dma_config.mem_range_valid && (dma_config.dst_asid == OtInternalAddr &&
                                                      dma_config.src_asid != OtInternalAddr);

      // Is this address a 'Clear Interrupt' operation?
      int_source = int_addr_lookup(item.a_addr);
      // Push addr item to destination queue
      dst_queue.push_back(item);
      `uvm_info(`gfn, $sformatf("Addr channel checks done for destination item"), UVM_HIGH)

      // Write to 'Clear Interrupt' address?
      if (int_source < 0) begin
        // Regular write traffic
        uint exp_a_mask_count_ones;
        uint num_bytes_this_txn;
        uint transfer_bytes_left;
        uint remaining_bytes;

        // Validate the write address for this destination access.
        check_addr(item.a_addr, exp_dst_addr, restricted, dma_config.get_write_fifo_en(),
                   dma_config.dst_addr, memory_range, dma_config, "Destination");

        // Note: this will only work because we KNOW that we don't reprogram the `chunk_data_size`
        //       register, so we can rely upon all non-final chunks being of the same size
        `DV_CHECK(num_bytes_transferred < dma_config.total_transfer_size,
                  "Write transaction when too many bytes transferred already");

        transfer_bytes_left = dma_config.total_transfer_size - num_bytes_transferred;
        // Bytes remaining until the end of the current chunk
        remaining_bytes = dma_config.chunk_data_size
                             - (num_bytes_transferred % dma_config.chunk_data_size);
        if (transfer_bytes_left < remaining_bytes) begin
          remaining_bytes = transfer_bytes_left;
        end

        exp_a_mask_count_ones = remaining_bytes > expected_per_txn_bytes ?
                                expected_per_txn_bytes : remaining_bytes;
        num_bytes_this_txn = $countones(item.a_mask);

        // check if a_mask matches the data size
        `DV_CHECK_EQ(num_bytes_this_txn, exp_a_mask_count_ones,
                 $sformatf("unexpected write a_mask: %x for %0d-byte transfer. Expected %x bytes",
                           item.a_mask, expected_per_txn_bytes, exp_a_mask_count_ones))

        // Check destination ASID for write transaction
        `DV_CHECK_EQ(if_name, cfg.asid_names[dma_config.dst_asid],
                     $sformatf("Unexpected write txn on %s interface with destination ASID %s",
                               if_name, dma_config.dst_asid.name()))

        // Track write-side progress through this transfer
        `uvm_info(`gfn, $sformatf("num_bytes_this_txn %x int_source %x",
                                  num_bytes_this_txn, int_source), UVM_HIGH);

        // On-the-fly checking of writing data
        check_write_data(if_name, item);

        // Check if opcode is as expected
        if ((dma_config.per_transfer_width != DmaXfer4BperTxn) ||
            (remaining_bytes < expected_per_txn_bytes)) begin
          `DV_CHECK(a_opcode inside {PutPartialData},
                    $sformatf("Unexpected opcode : %d on %s", a_opcode.name(), if_name))
        end else begin
          `DV_CHECK(a_opcode inside {PutFullData},
                    $sformatf("Unexpected opcode : %d on %s", a_opcode.name(), if_name))
        end

        // Update number of bytes transferred only in case of write txn - refer #338
        num_bytes_transferred += num_bytes_this_txn;

        // Update expectation of next destination access, predicting from our current expectation;
        // this is important because the current transaction address is missing its LSBs and thus
        // cannot be used.
        exp_dst_addr = predict_addr(exp_dst_addr, num_bytes_transferred, dma_config.dst_addr,
                                    dma_config.handshake & (dma_config.direction == DmaSendData),
                                    dma_config, "Destination");
      end else begin
        // Write to 'Clear Interrupt' address, so check the value written and the bus to which the
        // write has been sent.
        string exp_name;
        exp_name = dma_config.clear_int_bus[int_source] ? "host" : "ctn";

        `uvm_info(`gfn, $sformatf("Clear Interrupt write of 0x%0x to address 0x%0x",
                                  item.a_data, item.a_addr), UVM_HIGH)
        `DV_CHECK_EQ(if_name, exp_name,
                     $sformatf("%s received %s-targeted clear interrupt write", if_name, exp_name))
        `DV_CHECK_EQ(dma_config.int_src_wr_val[int_source], item.a_data,
                     $sformatf("Unexpected value 0x%0x written to clear interrupt %d", item.a_data,
                               int_source))
        `DV_CHECK_EQ(item.a_mask, 4'hF, "Unexpected write enables to clear interrupt write")

        // We're expecting only full word writes.
        `DV_CHECK(a_opcode inside {PutFullData},
                  $sformatf("Unexpected opcode : %d on %s", a_opcode.name(), if_name))
      end
    end

    // Update the expected value of memory buffer limit interrupt for this address
    exp_buffer_limit_intr = (dma_config.handshake & dma_config.auto_inc_buffer) &&
                            (item.a_addr >= dma_config.mem_buffer_limit ||
                             item.a_addr >= dma_config.mem_buffer_almost_limit);
    if (exp_buffer_limit_intr) begin
      `uvm_info(`gfn, $sformatf("Memory address:%0x crosses almost limit: 0x%0x limit: 0x%0x",
                                item.a_addr, dma_config.mem_buffer_almost_limit,
                                dma_config.mem_buffer_limit), UVM_LOW)  // UVM_HIGH)

      // Interrupt is expected only if enabled.
      exp_buffer_limit_intr = intr_enable_mem_limit;
    end

    // Track byte-counting within the transfer since it determines the prediction of completion
    `uvm_info(`gfn, $sformatf("num_bytes_transferred 0x%x total_transfer_size 0x%x",
                              num_bytes_transferred, dma_config.total_transfer_size), UVM_HIGH);

    // Update expected value of dma_done interrupt
    exp_dma_done_intr = (num_bytes_transferred >= exp_bytes_transferred) & intr_enable_done;
  endtask

  // Process items on Data channel
  task process_tl_data_txn(string if_name, ref tl_seq_item item);
    bit got_source_item = 0;
    bit got_dest_item = 0;
    uint queue_idx = 0;
    tl_d_op_e d_opcode = tl_d_op_e'(item.d_opcode);

    // Check if there is a previous address request with the
    // same source id as the current data request
    foreach (src_queue[i]) begin
      if (item.d_source == src_queue[i].a_source) begin
        got_source_item = 1;
        queue_idx = i;
        `uvm_info(`gfn, $sformatf("Found data item with source id %0d at index: %0d",
                                  item.d_source, queue_idx), UVM_HIGH)
      end
    end
    // Check if there is a previous address request with the
    // same destination id as the current data request
    if (!got_source_item) begin
      foreach (dst_queue[i]) begin
        if (item.d_source == dst_queue[i].a_source) begin
          got_dest_item = 1;
          queue_idx = i;
          `uvm_info(`gfn, $sformatf("Found data item with destination id %0d at index: %0d",
                                    item.d_source, queue_idx), UVM_HIGH)
        end
      end
    end

    // Check if Data item has an outstanding address item
    `DV_CHECK(got_source_item || got_dest_item,
              $sformatf("Data item source id doesn't match any outstanding request"))

    // Source interface item checks
    if (got_source_item) begin
      src_tl_error_detected = item.d_error;
      if (src_tl_error_detected) begin
        `uvm_info(`gfn, "Detected TL error on Source Data item", UVM_HIGH)
      end
      // Check if data item opcode is as expected
      `DV_CHECK(d_opcode inside {AccessAckData},
                $sformatf("Invalid opcode %s for source data item", d_opcode))
      // Delete after all checks related to data channel are done
      `uvm_info(`gfn, $sformatf("Deleting element at %d index in source queue", queue_idx),
                UVM_HIGH)
      src_queue.delete(queue_idx);
    end else if (got_dest_item) begin
      // Destination interface item checks
      dst_tl_error_detected = item.d_error;
      if (dst_tl_error_detected) begin
        `uvm_info(`gfn, "Detected TL error on Destination Data item", UVM_HIGH)
      end
      // Check if data item opcode is as expected
      `DV_CHECK(d_opcode inside {AccessAck},
                $sformatf("Invalid opcode %s for destination data item", d_opcode))
      // Delete after all checks related to data channel are done
      `uvm_info(`gfn, $sformatf("Deleting element at %d index in destination queue", queue_idx),
                UVM_HIGH)
      dst_queue.delete(queue_idx);
    end

    // Errors are expected to raise an interrupt if enabled, but we not must forget a configuration
    // error whilst error-free 'clear interrupt' writes are occurring.
    exp_dma_err_intr = exp_dma_err_intr | (item.d_error & intr_enable_error);
  endtask

  // Method to process requests on TL interfaces
  task process_tl_txn(string if_name,
                      uvm_tlm_analysis_fifo#(tl_channels_e) dir_fifo,
                      uvm_tlm_analysis_fifo#(tl_seq_item) a_chan_fifo,
                      uvm_tlm_analysis_fifo#(tl_seq_item) d_chan_fifo);
    bit exp_int_clearing;
    tl_channels_e dir;
    tl_seq_item   item;
    fork
      forever begin
        dir_fifo.get(dir);
        // Clear Interrupt writes are emitted even for invalid configurations.
        exp_int_clearing = dma_config.handshake & |dma_config.clear_int_src &
                          |dma_config.handshake_intr_en;
        // Check if transaction is expected for a valid configuration
        `DV_CHECK_FATAL(dma_config.is_valid_config || exp_int_clearing,
                           $sformatf("transaction observed on %s for invalid configuration",
                                     if_name))
        // Check if there is any active operation, but be aware that the Abort functionality
        // intentionally does not wait for a bus response (this is safe because the design never
        // blocks/stalls the TL-UL response).
        `DV_CHECK_FATAL(operation_in_progress || abort_via_reg_write,
                        "Transaction detected with no active operation")
        case (dir)
          AddrChannel: begin
            `DV_CHECK_FATAL(a_chan_fifo.try_get(item),
                            "dir_fifo pointed at A channel, but a_chan_fifo empty")
            `uvm_info(`gfn, $sformatf("received %s a_chan %s item with addr: %0x and data: %0x",
                                      if_name,
                                      item.is_write() ? "write" : "read",
                                      item.a_addr,
                                      item.a_data), UVM_HIGH)
            process_tl_addr_txn(if_name, item);
            // Update num_fifo_reg_write
            if (num_fifo_reg_write > 0) begin
              `uvm_info(`gfn, $sformatf("Processed FIFO clear_int_src addr: %0x0x", item.a_addr),
                        UVM_DEBUG)
              num_fifo_reg_write--;
            end else begin
              // Set status bit after all FIFO interrupt clear register writes are done
              fifo_intr_cleared = 1;
            end
          end
          DataChannel: begin
            `DV_CHECK_FATAL(d_chan_fifo.try_get(item),
                            "dir_fifo pointed at D channel, but d_chan_fifo empty")
            `uvm_info(`gfn, $sformatf("received %s d_chan item with addr: %0x and data: %0x",
                                      if_name, item.a_addr, item.d_data), UVM_HIGH)
            process_tl_data_txn(if_name, item);
          end
          default: `uvm_fatal(`gfn, "Invalid entry in dir_fifo")
        endcase
      end
    join_none
  endtask

  // Clear internal variables on reset
  virtual function void reset(string kind = "HARD");
    super.reset();
    `uvm_info(`gfn, "Detected DMA reset", UVM_LOW)
    current_operation_valid = 1'b0;
    dma_config.reset_config();
    src_queue.delete();
    dst_queue.delete();
    operation_in_progress = 1'b0;
    num_bytes_read = 0;
    exp_bytes_transferred = 0;
    num_bytes_transferred = 0;
    num_bytes_checked = 0;
    src_tl_error_detected = 0;
    dst_tl_error_detected = 0;
    abort_via_reg_write = 0;
    exp_buffer_limit_intr = 0;
    exp_dma_done_intr = 0;
    exp_dma_err_intr = 0;
    fifo_intr_cleared = 0;
  endfunction

  // Method to check if DMA interrupt is expected
  task monitor_and_check_dma_interrupts(ref dma_seq_item dma_config);
    fork
      // DMA memory buffer limit interrupt check
      forever begin
        @(posedge cfg.intr_vif.pins[DMA_MEMORY_BUFFER_LIMIT_INTR]);
        if (!cfg.en_scb) continue;
        if (!cfg.under_reset) begin
          `DV_CHECK_EQ(exp_buffer_limit_intr, 1,
                       "Unexpected assertion of dma_memory_buffer_limit interrupt")
        end
      end
      // DMA Error interrupt check
      forever begin
        @(posedge cfg.intr_vif.pins[DMA_ERROR]);
        if (!cfg.en_scb) continue;
        if (!cfg.under_reset) begin
          `DV_CHECK_EQ(exp_dma_err_intr, 1, "Unexpected assertion of dma_error interrupt")
        end
      end
      // DMA done interrupt check
      forever begin
        @(posedge cfg.intr_vif.pins[DMA_DONE]);
        if (!cfg.en_scb) continue;
        if (!cfg.under_reset) begin
          `DV_CHECK_EQ(exp_dma_done_intr, 1, "Unexpected assertion of dma_done interrupt")
        end
      end
    join_none
  endtask

  // Task to monitor LSIO trigger and update scoreboard internal variables
  task monitor_lsio_trigger();
    fork
      begin
        forever begin
          uvm_reg_data_t handshake_en;
          uvm_reg_data_t handshake_intr_en;
          // Wait for at least one LSIoO trigger to be active and it is eanbled
          @(posedge cfg.dma_vif.handshake_i);
          handshake_en = `gmv(ral.control.hardware_handshake_enable);
          handshake_intr_en = `gmv(ral.handshake_interrupt_enable);
          // Update number of register writes expected in case at least one
          // of the enabled handshake interrupt is asserted
          if (handshake_en && (cfg.dma_vif.handshake_i & handshake_intr_en)) begin
            num_fifo_reg_write = $countones(clear_int_src);
            `uvm_info(`gfn,
                      $sformatf("Handshake mode: num_fifo_reg_write:%0d", num_fifo_reg_write),
                      UVM_HIGH)
          end
        end
      end
    join_none
  endtask

  function void check_phase(uvm_phase phase);
    if (!cfg.en_scb) return;
    begin // Check if there are unprocessed source items
      uint size = src_queue.size();
      `DV_CHECK_EQ(size, 0, $sformatf("%0d unhandled source interface transactions",size))
      // Check if there are unprocessed destination items
      size = dst_queue.size();
      `DV_CHECK_EQ(size, 0, $sformatf("%0d unhandled destination interface transactions",size))
    end
    // Check if DMA operation is in progress
    `DV_CHECK_EQ(operation_in_progress, 0, "DMA operation incomplete")
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    num_fifo_reg_write = 0;
    // Call process methods on TL fifo
    foreach (cfg.fifo_names[i]) begin
      process_tl_txn(cfg.fifo_names[i],
                     tl_dir_fifos[cfg.dma_dir_fifo[cfg.fifo_names[i]]],
                     tl_a_chan_fifos[cfg.dma_a_fifo[cfg.fifo_names[i]]],
                     tl_d_chan_fifos[cfg.dma_d_fifo[cfg.fifo_names[i]]]);
    end
    monitor_and_check_dma_interrupts(dma_config);
    monitor_lsio_trigger();
  endtask

  // Function to get the memory model data at provided address
  function bit [7:0] get_model_data(asid_encoding_e asid, bit [63:0] addr);
    case (asid)
      OtInternalAddr: return cfg.mem_host.read_byte(addr);
      SocControlAddr: return cfg.mem_ctn.read_byte(addr);
      SocSystemAddr : return cfg.mem_sys.read_byte(addr);
      default: begin
        `uvm_error(`gfn, $sformatf("Unsupported Address space ID %d", asid))
      end
    endcase
  endfunction

  // Function to retrieve the next byte written into the destination FIFO
  // Note: that this is destructive in that it pops the data from the FIFO
  function bit [7:0] get_fifo_data(asid_encoding_e asid, bit [63:0] addr);
    case (asid)
      OtInternalAddr: return cfg.fifo_host.read_byte(addr);
      SocControlAddr: return cfg.fifo_ctn.read_byte(addr);
      SocSystemAddr : return cfg.fifo_sys.read_byte(addr);
      default: begin
        `uvm_error(`gfn, $sformatf("Unsupported Address space ID %d", asid))
      end
    endcase
  endfunction

  // Utility function to check the contents of the destination memory/FIFO against the
  // corresponding reference source data.
  function void check_data(ref dma_seq_item dma_config, bit [63:0] src_addr, bit [63:0] dst_addr,
                           bit [31:0] src_offset, bit [31:0] size);
    // Is the destination a FIFO?
    bit dst_fifo = dma_config.get_write_fifo_en();

    `uvm_info(`gfn, $sformatf("Checking output data [0x%0x,0x%0x) against 0%0x byte(s) of source",
                              dst_addr, dst_addr + size, size), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("  (src_addr 0x%0x at reference offset 0x%0x)", src_addr, src_offset),
                              UVM_MEDIUM)

    for (int i = 0; i < size; i++) begin
      // For the source data we access the original randomized data that we chose
      bit [7:0] src_data = cfg.src_data[src_offset + i];
      bit [7:0] dst_data;

      if (dst_fifo) begin
        dst_data = get_fifo_data(dma_config.dst_asid, dst_addr);
      end else begin
        dst_data = get_model_data(dma_config.dst_asid, dst_addr);
      end
      `uvm_info(`gfn,
                $sformatf("checking src_addr = %0x data = %0x : dst_addr = %0x data = %0x",
                          src_addr, src_data, dst_addr, dst_data), UVM_DEBUG)
      `DV_CHECK_EQ(src_data, dst_data,
                   $sformatf("src_addr = %0x data = %0x : dst_addr = %0x data = %0x",
                             src_addr, src_data, dst_addr, dst_data))
      src_addr++;
      if (!dst_fifo) begin
        dst_addr++;
      end
    end
  endfunction

  // Return the index that a register name refers to e.g. "int_source_addr_1" yields 1
  function uint get_index_from_reg_name(string reg_name);
    int str_len = reg_name.len();
    // Note: this extracts the final two characters which are either '_y' or 'xy',
    //       and because '_' is permitted in (System)Verilog numbers, it works for 0-99
    string index_str = reg_name.substr(str_len-2, str_len-1);
    return index_str.atoi();
  endfunction

  // Method to process DMA register write
  function void process_reg_write(tl_seq_item item, uvm_reg csr);
    `uvm_info(`gfn, $sformatf("Got reg_write to %s with addr : %0x and data : %0x ",
                              csr.get_name(), item.a_addr, item.a_data), UVM_HIGH)
    // incoming access is a write to a valid csr, so make updates right away
    void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

    case (csr.get_name())
      "intr_enable": begin
        `uvm_info(`gfn, $sformatf("Got intr_enable = %0x", item.a_data), UVM_HIGH)
        intr_enable_done      = item.a_data[DMA_DONE];
        intr_enable_error     = item.a_data[DMA_ERROR];
        intr_enable_mem_limit = item.a_data[DMA_MEMORY_BUFFER_LIMIT_INTR];
      end
      "source_address_lo": begin
        dma_config.src_addr[31:0] = item.a_data;
        `uvm_info(`gfn, $sformatf("Got source_address_lo = %0x",
                                  dma_config.src_addr[31:0]), UVM_HIGH)
      end
      "source_address_hi": begin
        dma_config.src_addr[63:32] = item.a_data;
        `uvm_info(`gfn, $sformatf("Got source_address_hi = %0x",
                                  dma_config.src_addr[63:32]), UVM_HIGH)
      end
      "destination_address_lo": begin
        dma_config.dst_addr[31:0] = item.a_data;
        `uvm_info(`gfn, $sformatf("Got destination_address_lo = %0x",
                                  dma_config.dst_addr[31:0]), UVM_HIGH)
      end
      "destination_address_hi": begin
        dma_config.dst_addr[63:32] = item.a_data;
        `uvm_info(`gfn, $sformatf("Got destination_address_hi = %0x",
                                  dma_config.dst_addr[63:32]), UVM_HIGH)
      end
      "address_space_id": begin
        // Get mirrored field value and cast to associated enum in dma_config
        dma_config.src_asid = asid_encoding_e'(`gmv(ral.address_space_id.source_asid));
        `uvm_info(`gfn, $sformatf("Got source address space id : %s",
                                  dma_config.src_asid.name()), UVM_HIGH)
        // Get mirrored field value and cast to associated enum in dma_config
        dma_config.dst_asid = asid_encoding_e'(`gmv(ral.address_space_id.destination_asid));
        `uvm_info(`gfn, $sformatf("Got destination address space id : %s",
                                  dma_config.dst_asid.name()), UVM_HIGH)
      end
      "enabled_memory_range_base": begin
        if (dma_config.mem_range_lock == MuBi4True) begin
          dma_config.mem_range_base = item.a_data;
          `uvm_info(`gfn, $sformatf("Got enabled_memory_range_base = %0x",
                                    dma_config.mem_range_base), UVM_HIGH)
        end
      end
      "enabled_memory_range_limit": begin
        if (dma_config.mem_range_lock == MuBi4True) begin
          dma_config.mem_range_limit = item.a_data;
          `uvm_info(`gfn, $sformatf("Got enabled_memory_range_limit = %0x",
                                    dma_config.mem_range_limit), UVM_HIGH)
        end
      end
      "range_valid": begin
        if (dma_config.mem_range_lock == MuBi4True) begin
          dma_config.mem_range_valid = `gmv(ral.range_valid.range_valid);
          `uvm_info(`gfn, $sformatf("Got mem_range_valid = %x",
                                    dma_config.mem_range_valid), UVM_HIGH)
        end
      end
      "range_regwen": begin
        // Get mirrored field value and cast to associated enum in dma_config
        dma_config.mem_range_lock = mubi4_t'(`gmv(ral.range_regwen.regwen));
        `uvm_info(`gfn, $sformatf("Got range register lock = %s",
                                  dma_config.mem_range_lock.name()), UVM_HIGH)
      end
      "total_data_size": begin
        dma_config.total_transfer_size = item.a_data;
        `uvm_info(`gfn, $sformatf("Got total_transfer_size = %0x B",
                                  dma_config.total_transfer_size), UVM_HIGH)
      end
      "chunk_data_size": begin
        dma_config.chunk_data_size = item.a_data;
        `uvm_info(`gfn, $sformatf("Got chunk_data_size = %0x B",
                                  dma_config.chunk_data_size), UVM_HIGH)
      end
      "transfer_width": begin
        dma_config.per_transfer_width = dma_transfer_width_e'(
                                            `gmv(ral.transfer_width.transaction_width));
        `uvm_info(`gfn, $sformatf("Got transfer_width = %s",
                                  dma_config.per_transfer_width.name()), UVM_HIGH)
      end
      "destination_address_limit_lo": begin
        dma_config.mem_buffer_limit[31:0] =
          `gmv(ral.destination_address_limit_lo.address_limit_lo);
      end
      "destination_address_limit_hi": begin
        dma_config.mem_buffer_limit[63:32] =
          `gmv(ral.destination_address_limit_hi.address_limit_hi);
      end
      "destination_address_almost_limit_lo": begin
        dma_config.mem_buffer_almost_limit[31:0] =
          `gmv(ral.destination_address_almost_limit_lo.address_limit_lo);
      end
      "destination_address_almost_limit_hi": begin
        dma_config.mem_buffer_almost_limit[63:32] =
          `gmv(ral.destination_address_almost_limit_hi.address_limit_hi);
      end
      "clear_int_bus": begin
        dma_config.clear_int_bus = `gmv(ral.clear_int_bus.bus);
      end
      "clear_int_src": begin
        dma_config.clear_int_src = `gmv(ral.clear_int_src.source);
        clear_int_src = dma_config.clear_int_src;
      end
      "sha2_digest_0",
      "sha2_digest_1",
      "sha2_digest_2",
      "sha2_digest_3",
      "sha2_digest_4",
      "sha2_digest_5",
      "sha2_digest_6",
      "sha2_digest_7",
      "sha2_digest_8",
      "sha2_digest_9",
      "sha2_digest_10",
      "sha2_digest_11",
      "sha2_digest_12",
      "sha2_digest_13",
      "sha2_digest_14",
      "sha2_digest_15": begin
        `uvm_error(`gfn, $sformatf("this reg does not have write access: %0s",
                                       csr.get_full_name()))
      end
      "int_source_addr_0",
      "int_source_addr_1",
      "int_source_addr_2",
      "int_source_addr_3",
      "int_source_addr_4",
      "int_source_addr_5",
      "int_source_addr_6",
      "int_source_addr_7",
      "int_source_addr_8",
      "int_source_addr_9",
      "int_source_addr_10": begin
        int index;
        `uvm_info(`gfn, $sformatf("Update %s", csr.get_name()), UVM_DEBUG)
        index = get_index_from_reg_name(csr.get_name());
        dma_config.int_src_addr[index] = item.a_data;
      end
      "int_source_wr_val_0",
      "int_source_wr_val_1",
      "int_source_wr_val_2",
      "int_source_wr_val_3",
      "int_source_wr_val_4",
      "int_source_wr_val_5",
      "int_source_wr_val_6",
      "int_source_wr_val_7",
      "int_source_wr_val_8",
      "int_source_wr_val_9",
      "int_source_wr_val_10": begin
        int index;
        `uvm_info(`gfn, $sformatf("Update %s", csr.get_name()), UVM_DEBUG)
        index = get_index_from_reg_name(csr.get_name());
        dma_config.int_src_wr_val[index] = item.a_data;
      end
      "control": begin
        // Is this the very start of a DMA transfer, rather than each individual chunk?
        // Note: Abort overrides Go
        bit start_transfer = get_field_val(ral.control.go, item.a_data) &
                             get_field_val(ral.control.initial_transfer, item.a_data) &
                            !get_field_val(ral.control.abort, item.a_data);
        `uvm_info(`gfn, $sformatf("CONTROL register written as 0x%0x", item.a_data), UVM_MEDIUM);
        // Update the 'Aborted' prediction in response to setting the CONTROL.abort bit
        // Note: this is a Write Only field so we cannot use the mirrored value
        abort_via_reg_write = get_field_val(ral.control.abort, item.a_data);
        if (abort_via_reg_write) begin
          `uvm_info(`gfn, "Aborting operation", UVM_LOW)
        end
        // Test bench/firmware is permitted to write to the Control register at the start of each
        // chunk but we must not reset our internal state; for non-initial chunks the Control
        // register write is just a nudge to proceed
        if (start_transfer) begin
          `uvm_info(`gfn, $sformatf("Got Start_Transfer = %0b", start_transfer), UVM_HIGH)
          // Get mirrored field value and cast to associated enum in dma_config
          dma_config.opcode = opcode_e'(`gmv(ral.control.opcode));
          `uvm_info(`gfn, $sformatf("Got opcode = %s", dma_config.opcode.name()), UVM_HIGH)
          // Get handshake mode enable bit
          dma_config.handshake = `gmv(ral.control.hardware_handshake_enable);
          `uvm_info(`gfn, $sformatf("Got hardware_handshake_mode = %0b", dma_config.handshake),
                    UVM_HIGH)
          // Get auto-increment bit
          dma_config.auto_inc_buffer = `gmv(ral.control.memory_buffer_auto_increment_enable);
          dma_config.auto_inc_fifo = `gmv(ral.control.fifo_auto_increment_enable);
          dma_config.direction = dma_control_data_direction_e'(`gmv(ral.control.data_direction));

          `uvm_info(`gfn, $sformatf("dma_config\n %s",
                                    dma_config.sprint()), UVM_HIGH)
          // Check if configuration is valid
          operation_in_progress = 1'b1;
          exp_src_addr = dma_config.src_addr;
          exp_dst_addr = dma_config.dst_addr;
          dma_config.is_valid_config = dma_config.check_config("scoreboard starting transfer");
          `uvm_info(`gfn, $sformatf("dma_config.is_valid_config = %b",
                                    dma_config.is_valid_config), UVM_MEDIUM)
          exp_dma_err_intr = !dma_config.is_valid_config & intr_enable_error;
          // Expect digest to be cleared even for rejected configurations
          exp_digest = '{default:0};
          if (cfg.en_cov) begin
            // Sample dma configuration
            cov.config_cg.sample(.dma_config (dma_config),
                                 .abort (abort_via_reg_write),
                                 .write_to_dma_mem_register(1'b0),
                                 .tl_src_err (1'b0),
                                 .tl_dst_err (1'b0));
          end
          // Clear status variables
          num_bytes_read = 0;
          num_bytes_transferred = 0;
          num_bytes_checked = 0;
          fifo_intr_cleared = 0;
          // Expectation of bytes transferred before the first 'Done' signal
          exp_bytes_transferred = dma_config.handshake ? dma_config.total_transfer_size
                                                       : dma_config.chunk_size(0);
        end else if (!dma_config.handshake && get_field_val(ral.control.go, item.a_data)) begin
          // Nudging a multi-chunk memory-to-memory transfer to proceed.
          operation_in_progress = 1'b1;
          if (dma_config.direction == DmaSendData && !dma_config.auto_inc_buffer) begin
            // Source address shall rewind; chunks overlap.
            exp_src_addr = dma_config.src_addr;
          end
          if (dma_config.direction == DmaRcvData && !dma_config.auto_inc_buffer) begin
            // Destination address shall rewind; chunks overlap.
            exp_dst_addr = dma_config.dst_addr;
          end
          // In memory-to-memory mode, DV/FW is advancing to the next chunk
          exp_bytes_transferred += dma_config.chunk_size(exp_bytes_transferred);
        end
      end
      "handshake_interrupt_enable": begin
        dma_config.handshake_intr_en = `gmv(ral.handshake_interrupt_enable.mask);
        `uvm_info(`gfn,
                  $sformatf("Got handshake_intr_en = 0x%x", dma_config.handshake_intr_en), UVM_HIGH)
      end
      // TODO: we shall surely need to handle `status` register writes at some point
      "intr_enable": /* Nothing to be done presently */;
      default: begin
        // This message may indicate a failure to update the configuration in the scoreboard
        // so that it matches the configuration programmed into the DUT
        `uvm_info(`gfn, $sformatf("reg_write of `%s` not handled", csr.get_name()), UVM_MEDIUM)
      end
    endcase
  endfunction

  // Method to process DMA register read
  function void process_reg_read(tl_seq_item item, uvm_reg csr);
    // After reads, if do_read_check is set, compare the mirrored_value against item.d_data
    bit do_read_check = 1'b1;
    `uvm_info(`gfn, $sformatf("Got reg_read to %s with addr : %0x and data : %0x ",
                              csr.get_name(), item.a_addr, item.a_data), UVM_HIGH)
    case (csr.get_name())
      "intr_state": begin
        `uvm_info(`gfn, $sformatf("intr_state = %0x", item.d_data), UVM_MEDIUM)
        do_read_check = 1;
      end
      "status": begin
        bit busy, done, aborted, error, sha2_digest_valid;
        bit [DmaErrLast-1:0] error_code;
        bit exp_aborted = abort_via_reg_write;
        bit bus_error;

        do_read_check = 1'b0;
        busy = get_field_val(ral.status.busy, item.d_data);
        done = get_field_val(ral.status.done, item.d_data);
        aborted = get_field_val(ral.status.aborted, item.d_data);
        error = get_field_val(ral.status.error, item.d_data);
        error_code[DmaSourceAddrErr] = get_field_val(ral.error_code.src_address_error, item.d_data);
        error_code[DmaDestAddrErr]   = get_field_val(ral.error_code.dst_address_error, item.d_data);
        error_code[DmaOpcodeErr]     = get_field_val(ral.error_code.opcode_error, item.d_data);
        error_code[DmaSizeErr]       = get_field_val(ral.error_code.size_error, item.d_data);
        error_code[DmaBusErr]        = get_field_val(ral.error_code.bus_error, item.d_data);
        error_code[DmaBaseLimitErr]  = get_field_val(ral.error_code.base_limit_error, item.d_data);
        error_code[DmaRangeValidErr] = get_field_val(ral.error_code.range_valid_error, item.d_data);
        error_code[DmaAsidErr]       = get_field_val(ral.error_code.asid_error, item.d_data);
        sha2_digest_valid = get_field_val(ral.status.sha2_digest_valid, item.d_data);

        // Bus errors are distinct from configuration errors.
        bus_error = error_code[DmaBusErr];

        if (done || aborted || error) begin
          string reasons;
          if (done)    reasons = "Done ";
          if (aborted) reasons = {reasons, "Aborted "};
          if (error)   reasons = {reasons, "Error" };
          operation_in_progress = 1'b0;
          `uvm_info(`gfn, $sformatf("Detected end of DMA operation (%s)", reasons), UVM_MEDIUM)
          // Clear variables
          num_fifo_reg_write = 0;
        end
        // Check total data transferred at the end of DMA operation
        if (done && // `done` bit detected in STATUS
            !(aborted || error) && // no abort or error detected
           !(src_tl_error_detected || dst_tl_error_detected))
        begin // no TL error
            // Check if number of bytes transferred is as expected at this point in the transfer
            `DV_CHECK_EQ(num_bytes_transferred, exp_bytes_transferred,
                         $sformatf("act_data_size: %0d exp_data_size: %0d",
                                   num_bytes_transferred, exp_bytes_transferred))
        end
        // STATUS.aborted should only be true if we requested an Abort.
        // However, the transfer may just have completed successfully even if we did request an
        // Abort and it may even have terminated in response to a TL-UL error for some sequences.
        if (abort_via_reg_write) begin
          `DV_CHECK_EQ(|{aborted, bus_error, done}, 1'b1, "Transfer neither Aborted nor completed.")
        end else begin
          `DV_CHECK_EQ(aborted, 1'b0, "STATUS.aborted bit set when not expected")
        end
        if (cfg.en_cov) begin
          // Sample dma status and error code
          cov.status_cg.sample(.busy (busy),
                               .done (done),
                               .aborted (aborted),
                               .error (error));
          cov.error_code_cg.sample(.error_code (error_code));
        end
        // Check results after each chunk of the transfer (memory-to-memory) or after the complete
        // transfer (handshaking mode).
        if (dma_config.is_valid_config && done) begin
          if (num_bytes_transferred >= dma_config.total_transfer_size) begin
            // SHA digest (expecting zeros if unused)
            // When using inline hashing, sha2_digest_valid must be raised at the end
            if (dma_config.opcode inside {OpcSha256, OpcSha384, OpcSha512}) begin
              `DV_CHECK_EQ(sha2_digest_valid, 1, "Digest valid bit not set when done")
            end
            predict_digest(dma_config);
          end

          // Has all of the output already been checked?
          if (num_bytes_checked < num_bytes_transferred) begin
            bit [31:0] check_bytes = num_bytes_transferred - num_bytes_checked;
            bit [63:0] dst_addr = dma_config.dst_addr;
            bit [63:0] src_addr = dma_config.src_addr;

            if (!dma_config.handshake ||
                (dma_config.direction == DmaSendData && dma_config.auto_inc_buffer)) begin
              src_addr += num_bytes_checked;
            end
            if (!dma_config.handshake ||
                (dma_config.direction == DmaRcvData && dma_config.auto_inc_buffer)) begin
              dst_addr += num_bytes_checked;
            end

            // TODO: we are still unable to check the final output data after the transfer if
            // overwriting has occurred; this will happen with a memory source/destination that
            // doesn't auto increment after each chunk, _or_ with a FIFO target that is actually
            // using a memory model because auto increment is enabled.
            if (dma_config.handshake && (!dma_config.auto_inc_buffer ||
                 (dma_config.direction == DmaSendData && dma_config.auto_inc_fifo))) begin
              `uvm_info(`gfn, "Unable to check output data because of chunks overlapping", UVM_LOW)
            end else begin
              check_data(dma_config, src_addr, dst_addr, num_bytes_checked, check_bytes);
              num_bytes_checked += check_bytes;
            end
          end
        end
      end
      // Register read check for lock register
      "range_regwen": begin
        do_read_check = 1'b0;
      end
      "sha2_digest_0",
      "sha2_digest_1",
      "sha2_digest_2",
      "sha2_digest_3",
      "sha2_digest_4",
      "sha2_digest_5",
      "sha2_digest_6",
      "sha2_digest_7",
      "sha2_digest_8",
      "sha2_digest_9",
      "sha2_digest_10",
      "sha2_digest_11",
      "sha2_digest_12",
      "sha2_digest_13",
      "sha2_digest_14",
      "sha2_digest_15": begin
        int digest_idx = get_index_from_reg_name(csr.get_name());
        // By default, the hardware outputs little-endian data for each digest (32 bits). But DPI
        // functions expect output to be big-endian. Thus we should flip the expected value if
        // digest_swap is zero.
        bit [TL_DW-1:0] real_digest_val;

        do_read_check = 1'b0;
        real_digest_val = {<<8{item.d_data}};
        `uvm_info(`gfn, $sformatf("Checking SHA digest calulated 0x%0x expected 0x%0x",
                                  real_digest_val, exp_digest[digest_idx]), UVM_MEDIUM)
        `DV_CHECK_EQ(real_digest_val, exp_digest[digest_idx]);
      end
      default: do_read_check = 1'b0;
    endcase

    if (do_read_check) begin
      `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, $sformatf("reg name: %0s",
                                                                    csr.get_full_name()))
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endfunction

  // Main method to process transactions on register configuration interface
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;

    bit write = item.is_write();

    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("\naccess unexpected addr 0x%0h", csr_addr))
    end

    // The access is to a valid CSR, now process it.
    // writes -> update local variable and fifo at A-channel access
    // reads  -> update predication at address phase and compare at D-channel access
    if (write && channel == AddrChannel) begin
      process_reg_write(item, csr);
    end  // addr_phase_write

    if (!write && channel == DataChannel) begin
      process_reg_read(item,csr);
    end  // data_phase_read
  endtask : process_tl_access

  // query the SHA model to get expected digest
  // update predicted digest to ral mirrored value
  virtual function void predict_digest(ref dma_seq_item dma_config);
    case (dma_config.opcode)
      OpcSha256: begin
        cryptoc_dpi_pkg::sv_dpi_get_sha256_digest(cfg.src_data, exp_digest[0:7]);
        exp_digest[8:15] = '{default:0};
      end
      OpcSha384: begin
        cryptoc_dpi_pkg::sv_dpi_get_sha384_digest(cfg.src_data, exp_digest[0:11]);
        exp_digest[12:15] = '{default:0};
      end
      OpcSha512: begin
        cryptoc_dpi_pkg::sv_dpi_get_sha512_digest(cfg.src_data, exp_digest[0:15]);
      end
      default: begin
        // When not using inline hashing mode
        exp_digest = '{default:0};
      end
    endcase
  endfunction

endclass
