// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A specialized sequence that runs each of the available binaries exactly once. This is used for
// directed tests when each causes an OTBN error, so you need to start a new operation for each.

class otbn_sequential_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_sequential_vseq)

  `uvm_object_new

  typedef string string_queue_t[$];

  // Get a list of all the paths to ELF files that we might use in the test, presented in a random
  // order.
  protected function string_queue_t list_elf_paths();
    chandle   helper;
    int       num_files;
    string    buffer;
    string    paths[$];

    // Check that cfg.otbn_elf_dir was set by the test
    `DV_CHECK_FATAL(cfg.otbn_elf_dir.len() > 0);

    // Use a C++ helper over DPI (because you can't list a directory in pure SystemVerilog). To do
    // so, we have to construct a helper object, which will look after memory allocation for the
    // string holding the path.
    helper = OtbnTestHelperMake(cfg.otbn_elf_dir);
    `DV_CHECK_FATAL(helper != null)

    // Ask the helper how many files there are. If it returns zero, the directory name is bogus or
    // the directory is empty.
    num_files = OtbnTestHelperCountFilesInDir(helper);
    `DV_CHECK_FATAL(num_files > 0,
                    $sformatf("No regular files found in directory `%0s'.", cfg.otbn_elf_dir))

    // Get each path from the C++ code. OtbnTestHelperGetFilePath returns the empty string on error.
    for (int idx = 0; idx < num_files; idx++) begin
      buffer = OtbnTestHelperGetFilePath(helper, idx);
      `DV_CHECK_FATAL(buffer.len() > 0, "Bad index for ELF file")

      // Take a copy of the string so that we can safely call OtbnTestHelperGetFilePath on the next
      // iteration (or free helper) without trashing the string we just got.
      buffer = $sformatf("%0s", buffer);

      paths.push_back(buffer);
    end

    OtbnTestHelperFree(helper);

    // Finally, shuffle paths before returning them
    paths.shuffle();
    return paths;
  endfunction

  task body();
    string paths[$] = list_elf_paths();
    foreach (paths[i]) begin
      `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", paths[i]), UVM_LOW)
      load_elf(paths[i], 1'b0);
      run_otbn();
    end
  endtask

endclass
