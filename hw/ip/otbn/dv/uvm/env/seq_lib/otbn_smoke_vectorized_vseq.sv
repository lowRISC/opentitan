// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A smoke test sequence for the vectorized instructions. This loads up the fixed
// "smoke_test_vectorized.elf" binary and forces everything to be in "simple" mode.

class otbn_smoke_vectorized_vseq extends otbn_smoke_vseq;
  `uvm_object_utils(otbn_smoke_vectorized_vseq)
  `uvm_object_new

  // Override pick_elf_path to always choose "smoke_test_vectorized.elf"
  protected function string pick_elf_path();
    // Check that cfg.otbn_elf_dir was set by the test
    `DV_CHECK_FATAL(cfg.otbn_elf_dir.len() > 0);

    return $sformatf("%0s/smoke_test_vectorized.elf", cfg.otbn_elf_dir);
  endfunction

endclass
