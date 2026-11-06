// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Loads the fixed "urnd_ctrl_test.elf" binary, enables the URND control feature and runs it.
//
// The URND control feature is gated by CTRL bit[2] (urnd_ctrl_enabled), which the DUT only latches
// while it is idle. The OTBN program cannot set this host register itself, so we write it here after
// the power-on secure wipe has finished.

class otbn_urnd_ctrl_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_urnd_ctrl_vseq)
  `uvm_object_new

  // Override pick_elf_path to always choose "urnd_ctrl_test.elf"
  protected function string pick_elf_path();
    `DV_CHECK_FATAL(cfg.otbn_elf_dir.len() > 0);

    return $sformatf("%0s/urnd_ctrl_test.elf", cfg.otbn_elf_dir);
  endfunction

  task body();
    uvm_status_e txn_status;

    // Wait for OTBN to complete its secure wipe after reset and become Idle.  Otherwise, OTBN will
    // ignore writes to CTRL.
    wait(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle);

    `uvm_info(`gfn, "Enabling URND ctrl (CTRL.urnd_ctrl_enabled = 1)", UVM_LOW)
    ral.ctrl.urnd_ctrl_enabled.set(1'b1);
    ral.ctrl.update(.status(txn_status));
    if (cfg.under_reset) return;
    if (txn_status != UVM_IS_OK) `uvm_error(`gfn, "Updating CTRL failed.")

    // Set SW errors as fatal errors to simplify detection of an error.
    `uvm_info(`gfn, "Handle SW errors as fatal errors (CTRL.software_errs_fatal = 1)", UVM_LOW)
    ral.ctrl.software_errs_fatal.set(1'b1);
    ral.ctrl.update(.status(txn_status));
    if (cfg.under_reset) return;
    if (txn_status != UVM_IS_OK) `uvm_error(`gfn, "Updating CTRL failed.")

    // Run the test.
    super.body();
    // The test lets OTBN crash if something is wrong. Check if OTBN did not crash.
    `DV_CHECK_FATAL(cfg.model_agent_cfg.vif.status != otbn_pkg::StatusLocked,
                    "OTBN entered the locked state indicating something went wrong.")
    reset_if_locked();
  endtask : body

endclass
