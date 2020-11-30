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

  virtual protected function string pick_elf_path();
    chandle helper;
    int     num_files;
    string  elf_path;

    // Check that cfg.otbn_elf_dir was set by the test
    `DV_CHECK_FATAL(cfg.otbn_elf_dir.len() > 0);

    // Pick an ELF file to use in the test. We have to do this via DPI (because you can't list a
    // directory in pure SystemVerilog). To do so, we have to construct a helper object, which will
    // look after memory allocation for the string holding the path.
    helper = OtbnTestHelperMake(cfg.otbn_elf_dir);
    `DV_CHECK_FATAL(helper != null)

    // Ask the helper how many files there are. If it returns zero, the directory name is bogus or
    // the directory is empty.
    num_files = OtbnTestHelperCountFilesInDir(helper);
    `DV_CHECK_FATAL(num_files > 0,
                    $sformatf("No regular files found in directory `%0s'.", cfg.otbn_elf_dir))

    // Pick a file, any file... Note that we pick an index on the SV side so that we use the right
    // random seed. Then we convert back to a filename with another DPI call. If the result is the
    // empty string, something went wrong.
    elf_path = OtbnTestHelperGetFilePath(helper, $urandom_range(num_files - 1));
    `DV_CHECK_FATAL(elf_path.len() > 0, "Bad index for ELF file")

    // Use sformat in a trivial way to take a copy of the string, so we can safely free helper (and
    // hence the old elf_path) afterwards.
    elf_path = $sformatf("%0s", elf_path);

    // Now that we've taken a copy of elf_path, we can safely free the test helper.
    OtbnTestHelperFree(helper);

    return elf_path;
  endfunction

endclass : otbn_single_vseq
