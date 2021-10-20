// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program multiple times, resetting in the middle of runs

class otbn_reset_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_reset_vseq)

  int unsigned num_iters = 10;

  `uvm_object_new

  task body();
    string elf_path = pick_elf_path();

    for (int i = 0; i < num_iters; i++) begin
      int unsigned longest_run_mirror;

      // Load up the binary. Since we always load the same binary, we take a copy of longest_run_,
      // which would otherwise be splatted by load_elf.
      longest_run_mirror = longest_run_;
      `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
      load_elf(elf_path, 1'b1);
      longest_run_ = longest_run_mirror;

      // Start OTBN. When the task returns, we'll be part-way through a run.
      start_running_otbn(.check_end_addr(1'b1));

      // If this isn't the last iteration, reset the DUT
      if (i + 1 < num_iters) begin
        dut_init("HARD");
      end
    end
  endtask

endclass
