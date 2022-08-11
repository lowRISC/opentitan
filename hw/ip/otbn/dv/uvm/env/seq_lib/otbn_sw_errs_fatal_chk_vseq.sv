// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_sw_errs_fatal_chk_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_sw_errs_fatal_chk_vseq)
  `uvm_object_new

  task body();
    // Wait for OTBN to complete its secure wipe after reset and become Idle.  Otherwise, OTBN will
    // ignore writes of `CTRL.software_errs_fatal`.
    wait(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle);
    // Set ctrl.software_errs_fatal. This change also will be passed to our model through
    // otbn_scoreboard.
    csr_utils_pkg::csr_wr(ral.ctrl, 'b1);
    super.body();
    reset_if_locked();
  endtask : body

endclass : otbn_sw_errs_fatal_chk_vseq
