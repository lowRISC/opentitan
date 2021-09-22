// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program multiple times, resetting in the middle of runs

class otbn_reset_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_reset_vseq)

  int unsigned num_iters = 10;

  `uvm_object_new

  task body();
    int max_cycles;
    string elf_path;

    elf_path = pick_elf_path();
    max_cycles = 1000;

    for (int i = 0; i < num_iters; i++) begin
      int cycle_counter;
      int reset_wait;
      bit timed_out = 1'b0;

      `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
      load_elf(elf_path, 1'b1);

      // Guess the number of cycles until reset. The first time around, we pick any number between 1
      // and 1,000. After that, we replace "1,000" with "75% of the longest we've seen the sequence
      // run before terminating". This should avoid problems where we keep resetting after the
      // sequence has finished.
      reset_wait = $urandom_range(max_cycles * 3 / 4) + 1;

      fork
        run_otbn();
        begin
          repeat (reset_wait) begin
            @(cfg.clk_rst_vif.cb);
            cycle_counter++;
          end
          timed_out = 1'b1;
        end
      join_any

      // When we get here, we know that either the OTBN sequence finished (in which case timed_out =
      // 1'b0) or we timed out. If the OTBN sequence finished, kill the counter process. We don't
      // kill the run_otbn task: it will spot a reset and terminate on its own.
      if (!timed_out) begin
        // If the OTBN sequence finished, update max_cycles. cycle_counter should always be less
        // than max_cycles (because of how we calculate reset_wait).
        `DV_CHECK_FATAL(cycle_counter < max_cycles);
        max_cycles = cycle_counter;
        disable fork;
      end

      // If this isn't the last iteration, or if we timed out, reset the DUT
      if (timed_out || i + 1 < num_iters) begin
        dut_init("HARD");
      end
    end
  endtask

endclass
