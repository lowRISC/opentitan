// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that exercises the flow defined in the wfi_test.s program. Exercises DMEM writes and
// reads whilst paused.

class otbn_wfi_smoke_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_wfi_smoke_vseq)
  `uvm_object_new

  // How long to stay in the PAUSED state.
  int unsigned min_resume_delay = 1;
  int unsigned max_resume_delay = 15;

  // The addresses for the in/output locations. Note, mem_rd/wr take the offset as 32-bit word and
  // not as byte address. So we must divide by 4.
  int input_addr = 0;
  int output_addr = 32 / 4;

  // Override pick_elf_path to always choose the directed test program.
  protected function string pick_elf_path();
    // Check that cfg.otbn_elf_dir was set by the test
    `DV_CHECK_FATAL(cfg.otbn_elf_dir.len() > 0);

    return $sformatf("%0s/wfi_test.elf", cfg.otbn_elf_dir);
  endfunction

  task body();
    string elf_path = pick_elf_path();
    bit [31:0] wr_value;
    bit [31:0] rd_value;

    cfg.clk_rst_vif.wait_for_reset(.wait_negedge(1'b0), .wait_posedge(1'b1));

    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
    load_elf(elf_path, .backdoor(1'b1));

    // Enable the WFI instruction. CTRL can only be configured while OTBN is idle.
    `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle)
    `uvm_info(`gfn, "Enabling WFI (CTRL.wfi_enabled = 1)", UVM_LOW)
    csr_utils_pkg::csr_wr(ral.ctrl, 32'h2);

    // Enable the DONE interrupt which is fired when OTBN gets paused.
    `uvm_info(`gfn, "Enabling the DONE interrupt", UVM_LOW)
    cfg_interrupts(.interrupts(1'b1), .enable(1'b1));

    // Write the value, start or resume and then check after the pause.
    for (int unsigned pause = 0; pause < 2; pause++) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(wr_value)
      `uvm_info(`gfn, $sformatf("Writing value to DMEM: 0x%08x @ 0x0", wr_value), UVM_LOW)
      csr_utils_pkg::mem_wr(ral.dmem, input_addr, wr_value);

      `uvm_info(`gfn, "Start or resume OTBN execution", UVM_LOW)
      csr_utils_pkg::csr_wr(ral.cmd, pause == 0 ? otbn_pkg::CmdExecute : otbn_pkg::CmdResume);

      // Wait for the interrupt, then check and clear it. Check also the STATUS register. Note that
      // the interrupt fires one cycle after STATUS changed to PAUSED. That is ok from a design
      // perspective.
      wait_for_interrupt();
      check_interrupts(.interrupts(1'b1), .check_set(1'b1), .clear(1'b1));
      csr_utils_pkg::csr_rd_check(.ptr(ral.status), .compare_value(otbn_pkg::StatusPaused));
      `uvm_info(`gfn, "Interrupt detected and STATUS is correct.", UVM_LOW)

      // Read and check the copied value.
      csr_utils_pkg::mem_rd(ral.dmem, output_addr, rd_value);
      `DV_CHECK_EQ_FATAL(wr_value, rd_value)
      `uvm_info(`gfn, "The read value matched the written one.", UVM_LOW)
    end

    // Disable the DONE interrupt and then let OTBN finish
    cfg_interrupts(.interrupts(1'b1), .enable(1'b0));
    csr_utils_pkg::csr_wr(ral.cmd, otbn_pkg::CmdResume);
    `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle)
    `uvm_info(`gfn, "OTBN finished after RESUME", UVM_LOW)

  endtask

endclass
