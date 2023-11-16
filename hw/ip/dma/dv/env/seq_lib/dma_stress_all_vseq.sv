// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Stress all DMA configurations and transfer properties, valid or invalid
class dma_stress_all_vseq extends dma_generic_vseq;
  `uvm_object_utils(dma_stress_all_vseq)
  `uvm_object_new

  // Constrain number of iterations and transactions in each iteration
  constraint transactions_c {num_txns inside {[10:40]};}
  constraint num_iters_c {num_iters inside {[5:20]};}

  bit operating;

  // Inter-task signaling
  event e_start;
  event e_stopped;

  // Retain the state of the 'regwen' that determines whether the DMA-enabled memory range has been
  // locked; modification of the range when writing is still enabled shall be avoid as it is
  // expected to induce failures.
  //
  // PR #20351 aims to protect all configuration throughout the transfer, at which point we shall
  // be permitted to attack many more registers.
  mubi4_t range_regwen;

  // Attempt to disrupt the DMA transfer by writing randomized data into the configuration registers
  virtual task modify_registers();
    // TODO: extend this to other configuration registers (see above).
    if (range_regwen != MuBi4True) begin
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
    end
  endtask

  // Transaction is commencing
  virtual task starting_txn(int unsigned txn, int unsigned num_txns, ref dma_seq_item dma_config);
    int pct = $urandom_range(0, 200);
    bit [31:0] data;

    super.starting_txn(txn, num_txns, dma_config);

    // Decide whether we want to randomly generate TL-UL bus errors during this transaction.
    enable_bus_errors((pct > 100) ? 0 : pct);

    // Retain the state of the 'REGWEN' field controlling the DMA-enabled memory range configuration
    csr_rd(cfg.ral.range_regwen, data);
    range_regwen = mubi4_t'(get_field_val(ral.range_regwen.regwen, data));

    operating = 1'b1;
    // Signal to the parallel test task that it should start generating events.
    ->e_start;
  endtask

  // Transaction has ended
  virtual task ending_txn(int unsigned txn, int unsigned num_txns, ref dma_seq_item dma_config,
                          status_t status);
    if (operating) begin
      // Stop our parallel task
      operating = 1'b0;
      wait (e_stopped.triggered);
    end
  endtask

  // The functionality of this vseq is implemented in `dma_generic_vseq` and restricted
  // to 'hardware handshaking' transfers in `dma_handshake_vseq`
  virtual task body();
    `uvm_info(`gfn, "DMA: Starting stress all Sequence", UVM_LOW)
    fork
      // Main test sequence
      super.body();
      // Parallel thread generates Aborts and Errors, and attempts to modify registers that should
      // be locked throughout the transaction.
      forever begin
        // Await a signal from the main task, indicating that we should start generating events.
        wait (e_start.triggered);
        while (operating) begin
          // Decide what to do, and when
          bit [31:0] event_delay = $urandom_range(10, 'h1fff);
          bit [3:0] event_rsn = $urandom_range(0, 15);
          while (operating && |event_delay) begin
            event_delay--;
            delay(1);
          end
          if (operating) begin
            unique case (event_rsn)
              2'b00: abort();
              // Introduce any other stressors here, eg. dynamically varying bus responsiveness.
              default: modify_registers();
            endcase
          end
        end
        // Signal to the main task that we have stopped trying to modify the range.
        ->e_stopped;
      end
    join_any
    disable fork;
    `uvm_info(`gfn, "DMA: Completed stress all Sequence", UVM_LOW)
  endtask : body
endclass
