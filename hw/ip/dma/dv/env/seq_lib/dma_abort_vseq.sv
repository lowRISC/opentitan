// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Aborting of both 'memory-to-memory' and 'hardware handshaking' DMA transfers
class dma_abort_vseq extends dma_generic_vseq;
  `uvm_object_utils(dma_abort_vseq)
  `uvm_object_new

  // Constrain number of iterations and transactions in each iteration; since aborting shall also
  // be exercised in the stress tests, keep this as a fairly short test of functionality.
  constraint transactions_c {num_txns inside {[4:12]};}
  constraint num_iters_c {num_iters inside {[2:4]};}

  bit operating;

  // Inter-task signaling
  event e_start;
  event e_stopped;

  // Permit only valid configurations for this test; with this sequence we're interested in Aborting
  // transfers, so generate only configurations that will not be immediately rejected.
  virtual function bit pick_if_config_valid();
    return 1'b1;
  endfunction

  // Choose whether to raise an Abort and, if so, after how many cycles.
  virtual function bit [15:0] choose_abort_delay();
    bit raise_abort;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(raise_abort, raise_abort dist { 0 := 20, 1 := 80};)
    return raise_abort ? $urandom_range(1, 16'h3FF) : 16'b0;
  endfunction

  // Transaction is commencing
  virtual task starting_txn(int unsigned txn, int unsigned num_txns, ref dma_seq_item dma_config);
    `DV_CHECK_EQ(operating, 1'b0, "Unexpected start of transaction")

    super.starting_txn(txn, num_txns, dma_config);

    operating = 1'b1;
    // Signal to the parallel test task it should start attempting to Abort the transfer.
    ->e_start;
  endtask

  // Transaction has ended
  virtual task ending_txn(int unsigned txn, int unsigned num_txns, ref dma_seq_item dma_config,
                          status_t status);
    `DV_CHECK_EQ(operating, 1'b1, "Unexpected end of transaction")
    // Stop our parallel task
    operating = 1'b0;
    wait (e_stopped.triggered);
  endtask

  // The functionality of this vseq is implemented in `dma_generic_vseq` and restricted
  // to 'memory-to-memory' transfers in `dma_memory_vseq`
  virtual task body();
    // Activate the generation of randomized Abort requests
    `uvm_info(`gfn, "DMA: Starting Abort Sequence", UVM_LOW)
    operating = 1'b0;
    fork
      // Run generic test body
      super.body();
      // Parallel task exercises aborting of DMA transfers
      forever begin
        bit [15:0] abort_delay;
        // Await a signal from the main task, indicating that the range should be locked.
        wait (e_start.triggered);
        `DV_CHECK_EQ(operating, 1'b1, "Abort thread triggered unexpectedly")
        // Decide whether or not to raise an Abort during this transfer and, if so, after how long.
        abort_delay = choose_abort_delay();
        if (|abort_delay) begin
          bit [8:0] abort_timeout = 0;
          while (operating && abort_delay > 0) begin
            abort_delay--;
            if (~|abort_delay) begin
              // Abort the transfer, and await below to be notified of its completion.
              abort();
            end
            delay(1);
          end
          // Aborts shall always be actioned, never ignored.
          // So, if completion does not occur within a small, finite time period (dominated by
          // the frequency of DV completion polling), this implies a failure.
          while (operating) begin
            abort_timeout++;
            `DV_CHECK(abort_timeout < 'h100, "Timeout responding to Abort request")
            delay(1);
          end
        end else begin
          // We've decided not to interrupt this transfer.
          while (operating) begin
            delay(100);
          end
        end
        ->e_stopped;
      end
    join_any
    `uvm_info(`gfn, "DMA: Completed Abort Sequence", UVM_LOW)
  endtask : body
endclass
