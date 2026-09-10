// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that exercises the flow defined in the wfi_test.s program. Exercises DMEM writes and
// reads whilst paused.

class otbn_wfi_smoke_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_wfi_smoke_vseq)
  `uvm_object_new

  // The in/output locations in DMEM, given as 32-bit word indices (mem_rd/mem_wr take an offset as
  // a word index and not as a byte address).
  int unsigned input_word_idx  = 0;
  int unsigned output_word_idx = 32 / 4;

  // Override pick_elf_path to always choose the directed test program.
  protected function string pick_elf_path();
    // Check that cfg.otbn_elf_dir was set by the test
    `DV_CHECK_FATAL(cfg.otbn_elf_dir.len() > 0);

    return $sformatf("%0s/wfi_test.elf", cfg.otbn_elf_dir);
  endfunction

  task body();
    string elf_path = pick_elf_path();
    uvm_status_e txn_status;

    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
    load_elf(elf_path, .backdoor(1'b1));

    // Wait for OTBN to finish any secure wipe and become idle. CTRL can only be configured while
    // OTBN is idle.
    wait(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle);

    `uvm_info(`gfn, "Enabling WFI (CTRL.wfi_enabled = 1)", UVM_LOW)
    ral.ctrl.wfi_enabled.set(1'b1);
    ral.ctrl.update(.status(txn_status));
    if (cfg.under_reset) return;
    if (txn_status != UVM_IS_OK) `uvm_error(`gfn, "Updating CTRL failed.")

    // Clear a possibly pending interrupt from load_elf() which could have issued a wipe.
    // The call to load_elf() might have issued a wipe, which would have caused OTBN to assert an
    // interrupt. Clear that interrupt if so.
    clear_all_interrupts();
    if (cfg.under_reset) return;

    // Enable the DONE interrupt, which is fired when OTBN gets paused.
    `uvm_info(`gfn, "Enabling the DONE interrupt", UVM_LOW)
    cfg_done_interrupt(1'b1);
    if (cfg.under_reset) return;

    // Start the binary, which should copy a value from input_word_idx to output_word_idx and then
    // stop with an interrupt. The run_segment task checks that the copying happened.
    run_segment(otbn_pkg::CmdExecute);
    if (cfg.under_reset) return;

    // Now resume the binary, which should copy a second value from input_word_idx to
    // output_word_idx before stopping again with an interrupt.
    run_segment(otbn_pkg::CmdResume);
    if (cfg.under_reset) return;

    // Let OTBN finish. We wait for the next DONE interrupt. OTBN then should be in idle. If not,
    // the test program has a bug and too many WFI instructions.
    csr_utils_pkg::csr_wr(ral.cmd, otbn_pkg::CmdResume);
    wait_for_interrupt();
    if (cfg.under_reset) return;
    clear_all_interrupts();
    `DV_CHECK_FATAL(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle,
                    "OTBN was not idle after resuming from the last WFI instruction. \
                     Check the test program.")

    `uvm_info(`gfn, "OTBN finished after RESUME", UVM_LOW)
  endtask

  // Run OTBN until it stops with a WFI instruction, then check that it has copied a value between
  // two locations.
  //  - Write a value to input_word_idx.
  //  - Start/Resume execution (run_command) until OTBN pauses on the next WFI instruction.
  //  - Read a value from output_word_idx.
  //  - Check that the value that was read is the value that was written.
  task run_segment(otbn_pkg::cmd_e run_command);
    bit [31:0] wr_value, rd_value;

    `DV_CHECK_STD_RANDOMIZE_FATAL(wr_value)

    // Write to input_word_idx
    `uvm_info(`gfn,
              $sformatf("Writing value to DMEM: 0x%08x @ 0x%0h", wr_value, 4 * input_word_idx),
              UVM_LOW)
    csr_utils_pkg::mem_wr(ral.dmem, input_word_idx, wr_value);
    if (cfg.under_reset) return;

    // Start or resume execution
    `uvm_info(`gfn, $sformatf("Writing %0s to CMD", run_command.name()), UVM_LOW)
    csr_utils_pkg::csr_wr(ral.cmd, run_command);
    if (cfg.under_reset) return;

    // Wait for the interrupt, then check and clear it.
    wait_for_interrupt();
    if (cfg.under_reset) return;
    check_done_interrupt(.check_set(1'b1), .clear(1'b1));
    if (cfg.under_reset) return;

    // At this point, STATUS should be PAUSED (letting us check the execution didn't run to
    // completion). Note, the STATUS register is updated earlier than the interrupt is active.
    csr_utils_pkg::csr_rd_check(.ptr(ral.status), .compare_value(otbn_pkg::StatusPaused));
    if (cfg.under_reset) return;

    // Finally, read from output_word_idx and check the result equals wr_value.
    csr_utils_pkg::mem_rd(ral.dmem, output_word_idx, rd_value);
    if (cfg.under_reset) return;

    if (rd_value != wr_value) begin
      `uvm_error(`gfn,
                 $sformatf({"The value read from output byte address, 0x%0h, is 0x%0h, which ",
                            "doesn't equal 0x%0h, the value that was written to input byte ",
                            "address 0x%0h."},
                           4 * output_word_idx, rd_value, wr_value, 4 * input_word_idx))
    end
  endtask

endclass
