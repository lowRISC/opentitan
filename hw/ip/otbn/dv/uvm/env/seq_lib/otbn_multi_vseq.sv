// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs multiple programs (or maybe the same program multiple times)

class otbn_multi_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_multi_vseq)

  // If we've already loaded a binary, we might decide to re-run it (this is going to be "more
  // back-to-back" because then we don't wait for the front-door load between runs). Make this
  // reasonably common.
  rand int rerun_pct;
  constraint rerun_pct_c {
    rerun_pct dist {
      0      :/ 1,
      [1:99] :/ 1,
      100    :/ 2
    };
  }

  `uvm_object_new

  task body();
    string elf_path;

    for (int i = 0; i < 10; i++) begin
      bit rerun = (i == 0) ? 1'b0 : ($urandom_range(100) <= rerun_pct);

      if (rerun) begin
        `uvm_info(`gfn, $sformatf("Re-using OTBN binary at `%0s'", elf_path), UVM_LOW)
      end else begin
        `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
        elf_path = pick_elf_path();
        load_elf(elf_path, 1'b0);
      end

      run_otbn();      
    end
  endtask

endclass
