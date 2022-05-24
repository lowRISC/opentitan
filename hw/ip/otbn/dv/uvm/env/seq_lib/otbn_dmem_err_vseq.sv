// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program multiple times and corrupts the
// dmem registers while the otbn is still running.

class otbn_dmem_err_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_dmem_err_vseq)

  `uvm_object_new

  task body();
    string elf_path;
    uvm_reg_data_t act_val;
    bit [38:0] mask;

    logic [127:0]    key;
    logic [63:0]     nonce;

    elf_path = pick_elf_path();
    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
    load_elf(elf_path, 1'b1);

    // Start OTBN running. When this task returns, we'll be in the middle of a run.
    start_running_otbn(.check_end_addr(1'b0));

    key = cfg.get_dmem_key();
    nonce = cfg.get_dmem_nonce();

    // Mask to corrupt 1 to 2 bits of the dmem memory
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)

    // Inject error at negedge of clock to avoid racing with second cycle of store instruction.
    @(cfg.clk_rst_vif.cbn);

    for (int i = 0; i < 2 * otbn_reg_pkg::OTBN_DMEM_SIZE / 32; i++) begin
      bit [ExtWLEN-1:0] old_data = cfg.read_dmem_word(i, key, nonce);
      bit [ExtWLEN-1:0] good_data = cfg.fix_integrity_wlen(old_data);
      bit [ExtWLEN-1:0] bad_data = good_data ^ {BaseWordsPerWLEN{mask}};
      cfg.write_dmem_word(i, bad_data, key, nonce);
    end

    cfg.model_agent_cfg.vif.invalidate_dmem();

    wait (cfg.model_agent_cfg.vif.status != otbn_pkg::StatusBusyExecute);

    // At this point, our status has changed. We're probably actually seeing the alert now, but make
    // sure that it has gone out in at most 100 cycles.
    reset_if_locked();

  endtask

endclass
