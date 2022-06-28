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

  // This bit dictates if end address check should happen or not. Set it to 0 if the check needs to
  // be disabled.
  bit do_end_addr_check = 1;

  `uvm_object_new

  task body();
    string elf_path;

    for (int i = 0; i < 10; i++) begin
      bit rerun = (i == 0) ? 1'b0 : ($urandom_range(100) <= rerun_pct);
      bit enable_interrupts = $urandom_range(100) < cfg.enable_interrupts_pct;
      bit irq_pin_high = cfg.intr_vif.sample_pin(0);
      bit clear_status = irq_pin_high ? ($urandom_range(100) < cfg.clear_irq_pct) : 1'b0;

      fork
        cfg_interrupts(enable_interrupts);
        if (clear_status) begin
          csr_utils_pkg::csr_wr(.ptr(ral.intr_state), .value(32'h1));
        end
        begin
          if (rerun) begin
            `uvm_info(`gfn, $sformatf("Re-using OTBN binary at `%0s'", elf_path), UVM_LOW)
          end else begin
            elf_path = pick_elf_path();
            `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
            load_elf(elf_path, 1'b0);
          end
        end
      join

      run_otbn(do_end_addr_check);
    end
  endtask

endclass
