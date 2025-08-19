// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence tests that the `CFG_REGWEN` lock prevents the configuration registers from
// being modified whilst the DUT is performing a transfer. By using hardware handshaking
// we can be confident that the DUT will remain busy between chunks and we can monitor the
// point of transitioning to the final chunk of the transfer.
// We thus avoid races between the DUT and this sequence.

class dma_config_lock_vseq extends dma_handshake_smoke_vseq;
  `uvm_object_utils(dma_config_lock_vseq)
  `uvm_object_new

  // Inter-task signaling
  event e_start; // Notification from the main task to the attacker that a transaction is starting.
  event e_stop; // Instruction from the main task to the attacker that it must stop.
  event e_stopped; // Notification that the attacker has stopped; the main task may reset the DUT.

  // The list of registers protected by CFG_REGWEN.
  uvm_reg cfg_csrs[$];

  // Collect all of the configuration registers that are protected by CFG_REGWEN.
  task cfgregs_collect();
    uvm_reg all_csrs[$];

    `uvm_info(`gfn, "List of CFG_REGWEN-controlled registers:", UVM_MEDIUM)
    ral.get_registers(all_csrs);
    foreach (all_csrs[i]) begin
      uvm_reg csr = all_csrs[i];
      if (ral.cfg_regwen.locks_reg_or_fld(csr)) begin
        `uvm_info(`gfn, $sformatf(" - Adding '%s'", csr.get_name()), UVM_MEDIUM)
        cfg_csrs.push_back(csr);
      end
    end
  endtask

  // Attempt to attack a configuration register; these should be protected by CFG_REGWEN
  // whilst the DMA controller is operating so the register contents should not change.
  task cfgreg_attack(uvm_reg csr);
    uvm_reg_data_t orig_val, val;
    csr_rd(csr, orig_val);
    `uvm_info(`gfn, $sformatf("Read %s 0x%0x", csr.get_name(), orig_val), UVM_MEDIUM)
    csr_wr(csr, ~orig_val);
    csr_rd(csr, val);
    `uvm_info(`gfn, $sformatf("Wrote %s 0x%0x -> read 0x%0x", csr.get_name(), ~orig_val, val),
              UVM_MEDIUM)
    `DV_CHECK_EQ(val, orig_val, "Configuration register no longer has expected value")
  endtask

  // Check that the CFG_REGWEN lock has the expected state.
  task cfgreg_check_lock(prim_mubi_pkg::mubi4_t exp_state);
    uvm_reg_data_t lock_val;
    csr_rd(ral.cfg_regwen, lock_val);
    `uvm_info(`gfn, $sformatf("CFG_REGWEN act 0x%0x exp 0x%0x", lock_val, exp_state), UVM_MEDIUM)
    `DV_CHECK_EQ(lock_val, exp_state, "CFG_REGWEN does not have expected state")
  endtask

  // Randomization of DMA configuration and transfer properties; here we are restricting the
  // permissible configuration and transfers to hardware handshaking copy operations consisting
  // of at least two chunks.
  // We may then safely attempt to modify the configuration registers up until the commencement
  // of the final chunk, confident that the DUT will not re-enable CFG_REGWEN in that time.
  virtual function void randomize_item(ref dma_seq_item dma_config);
    // Allow only valid DMA configurations
    dma_config.valid_dma_config = 1;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(
      dma_config,
      src_addr_inc & dst_addr_inc; // Prevent DUT from updating src/dst so we can attack them too
      src_addr[1:0] == dst_addr[1:0]; // Use same alignment for source and destination address
      total_data_size % 4 == 0; // Limit to multiples of 4B
      total_data_size >= 2 * chunk_data_size; // At least two chunks.
      chunk_data_size >= 'h80; // Chunk is long enough to attack a few registers.
      per_transfer_width == DmaXfer4BperTxn; // Limit to only 4B transfers
      handshake == 1'b1; // Enable hardware handshake mode
      handshake_intr_en != 0; // At least one handshake interrupt signal must be enabled
      opcode == OpcCopy;) // Avoid any involved operations such as SHA2 hashing
    `uvm_info(`gfn, $sformatf("DMA: Randomized a new transaction:%s",
                              dma_config.convert2string()), UVM_MEDIUM)
  endfunction

  // Transaction is commencing.
  virtual task starting_txn(int unsigned txn, int unsigned num_txns, ref dma_seq_item dma_config);
    super.starting_txn(txn, num_txns, dma_config);
    // Tell our parallel task that the transfer shall be _starting soon_.
    ->e_start;
  endtask

  // Transaction has ended.
  virtual task ending_txn(int unsigned txn, int unsigned num_txns, ref dma_seq_item dma_config,
                          status_t status);
    // Stop our parallel task
    ->e_stop;
    super.ending_txn(txn, num_txns, dma_config, status);
    wait (e_stopped.triggered);
  endtask

  virtual task body();
    `uvm_info(`gfn, "DMA: Starting 'config lock' sequence", UVM_LOW)
    // Collect a list of the registers that are controlled by the CFG_REGWEN lock.
    cfgregs_collect();
    fork
      begin : isolation_fork
        fork
          // Run smoke test body
          super.body();
          // Parallel task attempts to change the CFG_REGWEN-controlled registers.
          begin
            // Check the initial state of the CFG_REGWEN lock is as expected;
            // Await a signal from the main task, indicating that the range should be locked.
            cfgreg_check_lock(prim_mubi_pkg::MuBi4True);

            forever begin
              // Byte offset of the beginning of the final chunk within the transfer.
              int unsigned final_chunk_offset;

              // Wait for an indication that the DUT is _about to commence_ the transfer.
              wait (e_start.triggered);
              // Continue only after something has been read, indicating that it is active.
              while (!get_bytes_read(dma_config)) begin
                delay(16);  // Proceed soon after data reading occurs.
              end

              // Re-test the lock state; we must do this only _after_ we know the DUT is operating.
              cfgreg_check_lock(prim_mubi_pkg::MuBi4False);

              // Keep trying registers until the final chunk of the transfer is observed.
              final_chunk_offset = dma_config.total_data_size - dma_config.chunk_data_size;
              while (get_bytes_read(dma_config) < final_chunk_offset) begin
                // Choose a random register.
                int unsigned r = $urandom_range(cfg_csrs.size() - 1, 0);
                // Attempt to modify one of the configuration registers that should be locked by
                // CFGR_REGWEN.
                cfgreg_attack(cfg_csrs[r]);
                // Back off a little to allow other tasks access, but we _must_ poll
                // `get_bytes_read()` // often enough to be sure that the transfer does not complete
                // before we have stopped attacking the registers.
                delay($urandom_range(4, 12));
                // Re-read the state of the `cfg_regwen` lock.
              end
              // Await completion of the transfer.
              wait (e_stop.triggered);

              // Check the lock state one last time.
              cfgreg_check_lock(prim_mubi_pkg::MuBi4True);

              // Signal that we have finished reading CSRs; the main task may at this point proceed
              // to reset the DUT.
              ->e_stopped;
            end
          end
        join_any
        disable fork;
      end : isolation_fork
    join
    `uvm_info(`gfn, "DMA: Completed 'config lock' sequence", UVM_LOW)
  endtask : body
endclass
