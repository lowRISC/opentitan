// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A smoke test sequence. This loads up the fixed "smoke.elf" binary and forces everything to be in
// "simple" mode.

class otbn_smoke_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_smoke_vseq)
  `uvm_object_new

  constraint do_backdoor_load_c { do_backdoor_load == 1'b0; }

  // Override pick_elf_path to always choose "smoke.elf"
  protected function string pick_elf_path();
    // Check that cfg.otbn_elf_dir was set by the test
    `DV_CHECK_FATAL(cfg.otbn_elf_dir.len() > 0);

    return $sformatf("%0s/smoke.elf", cfg.otbn_elf_dir);
  endfunction

endclass
