// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence which injects a fatal error whilst OTBN is paused or gets paused by a WFI
// instruction. The injection either happens whilst paused or at a specific instruction address.
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

  // The address where we want to escalate. This points at the add instruction in the following
  // sequence in the program that is running:
  //
  //    add   x4, x2, x3
  //    wfi
  //
  // Escalation is delayed by one cycle, which means that it will happen at the same time as the WFI
  // instruction.
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
    string       insn_addr_path = {cfg.dut_instance_hier, ".u_otbn_core.insn_addr"};

    uvm_reg_data_t act_val;
    uvm_status_e   txn_status;

    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
    load_elf(elf_path, .backdoor(1'b1));

    // Wait for OTBN to finish any secure wipe and become idle. CTRL can only be configured while
    // OTBN is idle.
    wait(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle);

    `uvm_info(`gfn, "Enabling WFI insn", UVM_LOW)
    ral.ctrl.wfi_enabled.set(1'b1);
    ral.ctrl.update(.status(txn_status));
    if (cfg.under_reset) return;
    if (txn_status != UVM_IS_OK) `uvm_error(`gfn, "Updating CTRL failed.")

    // Start execution and wait for the chosen trigger point.
    run_until_trigger(inject_trigger, status_path, insn_addr_path);

    // Inject a fatal error and notify model.
    inject_error();

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

  // Repeatedly do reads of hdl_path using uvm_hdl_read on negedges of the clock until the result
  // (cast to 32 bits width) equals expected_value.
  //
  // Time out with a failure after max_cycles but return early on a reset.
  task backdoor_spinwait(string       hdl_path,
                         bit [31:0]   expected_value,
                         int unsigned max_cycles);
    fork : isolation_fork begin
      fork
        wait (cfg.under_reset);
        begin
          bit found = 1'b0;

          for (int unsigned i = 0; !found && (i < max_cycles); i++) begin
            bit [31:0] value;

            @(cfg.clk_rst_vif.cbn);
            if (!uvm_hdl_read(hdl_path, value)) begin
              `uvm_fatal(get_full_name(), $sformatf("Failed to read from %0s", hdl_path))
            end
            `uvm_info(`gfn, $sformatf("%0s is 0x%0h", hdl_path, value), UVM_HIGH)
            found = (value == expected_value);
          end

          if (!found) begin
            `uvm_error(get_full_name(),
                       $sformatf("Waited %0d cycles and the value at %0s didn't become 0x%0h.",
                                 max_cycles, hdl_path, expected_value))
          end
        end
      join_any
      disable fork;
    end join
  endtask

  // Start execution and wait for the chosen trigger point
  task run_until_trigger(inject_trigger_e trigger,
                         string           status_path,
                         string           insn_addr_path);
    `uvm_info(`gfn, "Starting OTBN execution", UVM_LOW)

    // Must be in a fork as returning from the csr_wr takes a while and we thus could miss an early
    // wfi insn address.
    fork
      csr_utils_pkg::csr_wr(ral.cmd, otbn_pkg::CmdExecute);
      begin
        if (trigger == INJECT_AT_PAUSE) begin
          `uvm_info(`gfn, "Waiting for OTBN to reach the PAUSED state", UVM_LOW)
          backdoor_spinwait(status_path, otbn_pkg::StatusPaused, 1000);
        end else begin
          `uvm_info(`gfn, $sformatf("Waiting for insn_addr == 0x%0h", inject_insn_addr), UVM_LOW)
          backdoor_spinwait(insn_addr_path, inject_insn_addr, 1000);
        end
      end
    join
  endtask

  // Inject a fatal error and notify the model. Release the error on the next negedge of the clock.
  task inject_error();
    string err_path = {cfg.dut_instance_hier, ".u_otbn_core.predec_error"};
    err_bits_reg_t err_bits;
    `uvm_info(`gfn, $sformatf("Forcing `%0s'", err_path), UVM_LOW)
    `DV_CHECK_FATAL(uvm_hdl_force(err_path, 1'b1) == 1)

    err_bits = '{bad_internal_state: 1'b1, default: 1'b0};
    cfg.model_agent_cfg.vif.send_err_escalation(err_bits);

    @(cfg.clk_rst_vif.cbn);
    `DV_CHECK_FATAL(uvm_hdl_release(err_path) == 1)
  endtask

endclass
