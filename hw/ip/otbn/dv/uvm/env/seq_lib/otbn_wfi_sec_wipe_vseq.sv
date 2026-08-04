// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence which injects a fatal error whilst OTBN is or gets paused by a WFI instruction.
// The injection either happens whilst paused or at a specific instruction address.
// The 2nd case allows to escalate exactly when the WFI instruction is executed, which is an edge
// case we would like to test.

class otbn_wfi_sec_wipe_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_wfi_sec_wipe_vseq)
  `uvm_object_new

  // Flag selecting when to inject the error.
  typedef enum bit {
    INJECT_AT_PAUSE,    // wait until OTBN reports the paused state (STATUS == PAUSED).
    INJECT_AT_INSN_ADDR // wait until the core fetches the instruction at inject_insn_addr.
  } inject_trigger_e;

  // TODO: Right now we just reseed this test 5x and hope that we see both cases. This should be
  //       ensured in a better way. Additionally, maybe we should also use different escalation
  //       sources? Now only one is used because the escalation sources should be tested with their
  //       own test.
  rand inject_trigger_e inject_trigger;

  // At which address we want to escalate. This targets the instruction just before the WFI
  // instruction because the escalation is delayed by 1 cycle. This instruction must be single
  // cycle, otherwise the escalation would happen too early.
  bit [31:0] inject_insn_addr = 32'h08;

  // Override pick_elf_path to always choose the directed test program.
  protected function string pick_elf_path();
    // Check that cfg.otbn_elf_dir was set by the test
    `DV_CHECK_FATAL(cfg.otbn_elf_dir.len() > 0);

    return $sformatf("%0s/wfi_sec_wipe.elf", cfg.otbn_elf_dir);
  endfunction

  task body();
    string       elf_path = pick_elf_path();
    string       status_path = {cfg.dut_instance_hier, ".status_d"};
    string       predec_err_path = {cfg.dut_instance_hier, ".u_otbn_core.predec_error"};
    string       insn_addr_path = {cfg.dut_instance_hier, ".u_otbn_core.insn_addr"};
    logic [7:0]  rtl_status;
    logic [31:0] rtl_insn_addr;

    otbn_pkg::err_bits_t err_bits;
    uvm_reg_data_t act_val;

    cfg.clk_rst_vif.wait_for_reset(.wait_negedge(1'b0), .wait_posedge(1'b1));

    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
    load_elf(elf_path, .backdoor(1'b1));

    `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle)

    // Enable the WFI instruction.
    `uvm_info(`gfn, "Enabling WFI insn", UVM_LOW)
    csr_utils_pkg::csr_wr(ral.ctrl, 32'h2);

    // Start execution and wait for the chosen trigger point. Must be in a fork as returning from
    // the csr_wr takes a while and we thus could miss an early wfi insn address.
    `uvm_info(`gfn, "Starting OTBN execution", UVM_LOW)
    fork
      csr_utils_pkg::csr_wr(ral.cmd, otbn_pkg::CmdExecute);
      begin
        if (inject_trigger == INJECT_AT_PAUSE) begin
          `uvm_info(`gfn, "Waiting for OTBN to reach the PAUSED state", UVM_LOW)
          `DV_SPINWAIT(
            do begin
              @(cfg.clk_rst_vif.cbn);
              `DV_CHECK_FATAL(uvm_hdl_read(status_path, rtl_status),
                              $sformatf("Failed to read STATUS from `%0s'", status_path))
            end while (rtl_status !== otbn_pkg::StatusPaused);,
            "Timed out waiting for OTBN to reach the PAUSED state")
        end else begin
          `uvm_info(`gfn, $sformatf("Waiting for insn_addr == 0x%0h", inject_insn_addr), UVM_LOW)
          `DV_SPINWAIT(
            do begin
              @(cfg.clk_rst_vif.cbn);
              `DV_CHECK_FATAL(uvm_hdl_read(insn_addr_path, rtl_insn_addr),
                              $sformatf("Failed to read insn_addr from `%0s'", insn_addr_path))
            end while (rtl_insn_addr !== inject_insn_addr);,
            "Timed out waiting for the target instruction address")
        end
      end
    join

    // Inject a fatal error and notify model.
    `uvm_info(`gfn, $sformatf("Forcing `%0s'", predec_err_path), UVM_LOW)
    `DV_CHECK_FATAL(uvm_hdl_force(predec_err_path, 1'b1) == 1)

    err_bits = '{reg_intg_violation: 1'b1, default: 1'b0};
    cfg.model_agent_cfg.vif.send_err_escalation(err_bits);

    @(cfg.clk_rst_vif.cbn);
    `DV_CHECK_FATAL(uvm_hdl_release(predec_err_path) == 1)

    // OTBN should now do a secure wipe
    wait_secure_wipe();

    // We should now be in a locked state after the secure wipe.
    `DV_CHECK_FATAL(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked);
    // The scoreboard will have seen the transition to locked state and inferred that it should
    // see a fatal alert. However, it doesn't really have a way to ensure that we keep generating
    // them. Wait for 3 fatal alerts and also read STATUS, ERR_BITS and FATAL_ALERT_CAUSE in
    // parallel.
    fork
      begin
        csr_utils_pkg::csr_rd(.ptr(ral.status), .value(act_val));
        csr_utils_pkg::csr_rd(.ptr(ral.err_bits), .value(act_val));
        csr_utils_pkg::csr_rd(.ptr(ral.fatal_alert_cause), .value(act_val));
      end
      begin
        repeat (3) wait_alert_trigger("fatal", .wait_complete(1));
      end
    join

    do_apply_reset = 1'b1;
    dut_init("HARD");
  endtask

endclass
