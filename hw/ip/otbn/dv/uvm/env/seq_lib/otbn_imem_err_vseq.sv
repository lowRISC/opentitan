// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program multiple times and corrupts the
// imem registers while the otbn is still running.

class otbn_imem_err_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_imem_err_vseq)

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

    key = cfg.get_imem_key();
    nonce = cfg.get_imem_nonce();

    @(cfg.clk_rst_vif.cbn);

    // Mask to corrupt 1 to 2 bits of the imem memory
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)

    `uvm_info(`gfn, "Injecting IMEM errors", UVM_MEDIUM)

    for (int i = 0; i < otbn_reg_pkg::OTBN_IMEM_SIZE / 4; i++) begin
      bit [BaseIntgWidth-1:0] old_data = cfg.read_imem_word(i, key, nonce);
      bit [BaseIntgWidth-1:0] good_data = cfg.fix_integrity_32(old_data);
      bit [BaseIntgWidth-1:0] bad_data = good_data ^ mask;
      cfg.write_imem_word(i, bad_data, key, nonce);
    end

    cfg.model_agent_cfg.vif.invalidate_imem();

    // If we were unlucky, we might have injected the errors while OTBN was executing an instruction
    // that was already causing it to stop. To allow for this specific case, we wait 100 cycles to
    // let that instruction flush through and secure wiping to finish.
    repeat (100) @(cfg.clk_rst_vif.cbn);
    // If OTBN is now idle, we hit this exact window and the test didn't do anything useful. Ho
    // hum... Note that we don't need to apply a reset in this case.
    if (cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle) begin
      `uvm_info(`gfn, "Skipping test: we happened to inject the IMEM error at a bad time", UVM_LOW)
      return;
    end

    // Looks like the injected error should have some effect. Wait until the ISS and RTL move to a
    // locked state.
    reset_if_locked();
  endtask

endclass
