// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A basic sequence that loads up an ELF file, lets it run to completion, and then finishes.

class otbn_single_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_single_vseq)
  `uvm_object_new

  // Should the ELF file be loaded with a backdoor DPI method, or should we actually generate the
  // bus transactions to load it into the memory properly?
  rand bit do_backdoor_load;

  constraint do_backdoor_load_c {
    do_backdoor_load dist { 1'b1 := cfg.backdoor_load_pct,
                            1'b0 := 100 - cfg.backdoor_load_pct };
  }

  task body();
    string elf_path = pick_elf_path();

    // Actually load the binary
    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
    load_elf(elf_path, do_backdoor_load);

    // We've loaded the binary. Run the processor to see what happens!
    run_otbn();
  endtask : body

endclass : otbn_single_vseq
