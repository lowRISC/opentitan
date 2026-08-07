// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests multiple WFI instructions executed back to back.

class otbn_wfi_back_to_back_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_wfi_back_to_back_vseq)
  `uvm_object_new

  // How long to stay in the PAUSED state.
  int unsigned min_resume_delay = 1;
  int unsigned max_resume_delay = 15;
  int unsigned num_pauses = 3;

  // Override pick_elf_path to always choose the directed test program.
  protected function string pick_elf_path();
    // Check that cfg.otbn_elf_dir was set by the test
    `DV_CHECK_FATAL(cfg.otbn_elf_dir.len() > 0);

    return $sformatf("%0s/wfi_back_to_back.elf", cfg.otbn_elf_dir);
  endfunction

  task body();
    string       elf_path = pick_elf_path();
    string       status_path = {cfg.dut_instance_hier, ".status_d"};
    logic [7:0]  rtl_status;
    int unsigned resume_delay;

    cfg.clk_rst_vif.wait_for_reset(.wait_negedge(1'b0), .wait_posedge(1'b1));

    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
    load_elf(elf_path, .backdoor(1'b1));

    // Wait for OTBN to finish its initial secure wipe and become idle. CTRL can only be configured
    // while OTBN is idle.
    `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle)

    `uvm_info(`gfn, "Enabling WFI (CTRL.wfi_enabled = 1)", UVM_LOW)
    csr_utils_pkg::csr_wr(ral.ctrl, 32'h2);

    // Start execution and wait for OTBN to reach the WFI instruction.
    `uvm_info(`gfn, "Starting OTBN execution", UVM_LOW)
    csr_utils_pkg::csr_wr(ral.cmd, otbn_pkg::CmdExecute);

    for (int unsigned i_pause = 0; i_pause < num_pauses; i_pause++) begin
      `uvm_info(`gfn, "Waiting for OTBN to reach the PAUSED state", UVM_LOW)
        `DV_SPINWAIT(
          do begin
            @(cfg.clk_rst_vif.cbn);
            `DV_CHECK_FATAL(uvm_hdl_read(status_path, rtl_status),
                            $sformatf("Failed to read STATUS from `%0s'", status_path))
          end while (rtl_status !== otbn_pkg::StatusPaused);,
          "Timed out waiting for OTBN to reach the PAUSED state")

      // Stay paused for a random number of cycles.
      resume_delay = $urandom_range(max_resume_delay, min_resume_delay);
      `uvm_info(`gfn,
                $sformatf("Pause %0d / %0d, waiting %2d cycles before RESUME",
                          i_pause + 1, num_pauses, resume_delay),
                UVM_LOW)
      cfg.clk_rst_vif.wait_clks(resume_delay);

      // Resume execution
      csr_utils_pkg::csr_wr(ral.cmd, otbn_pkg::CmdResume);
    end

    // Wait until the program has ended.
    `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle)
    `uvm_info(`gfn, "OTBN finished after RESUME", UVM_LOW)
  endtask

endclass
