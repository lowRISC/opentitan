// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A basic sanity test
//
// This loads up an ELF file, lets it run to completion, and then finishes.

class otbn_sanity_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_sanity_vseq)
  `uvm_object_new

  // The name of the ELF file to use in the test. Taken as a path relative to cfg.otbn_elf_dir.
  //
  // This is set in pre_start(), which will run after the vseq has been randomised. To customise it,
  // override pick_elf_name() respectively.
  string   elf_name;

  // Should the ELF file be loaded with a backdoor DPI method, or should we actually generate the
  // bus transactions to load it into the memory properly?
  rand bit do_backdoor_load;

  constraint do_backdoor_load_c {
    do_backdoor_load dist { 1'b1 := cfg.backdoor_load_pct,
                            1'b0 := 100 - cfg.backdoor_load_pct };
  }

  task pre_start();
    super.pre_start();
    elf_name = pick_elf_name();
  endtask

  task body();
    load_elf(elf_name, do_backdoor_load);

    `uvm_error(`gfn, "ELF loaded. Now what?")
  endtask : body

  // Return a (random) choice of ELF file to be stored in elf_name
  virtual function automatic string pick_elf_name();
    // TODO: Pick something more interesting here!
    return "0.elf";
  endfunction

endclass : otbn_sanity_vseq
