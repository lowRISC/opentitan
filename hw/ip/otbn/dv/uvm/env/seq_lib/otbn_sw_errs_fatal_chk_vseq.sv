// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_sw_errs_fatal_chk_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_sw_errs_fatal_chk_vseq)
  `uvm_object_new

  task body();
    // Set ctrl.software_errs_fatal.
    csr_utils_pkg::csr_wr(ral.ctrl, 'b1);
    // When set software errors produce fatal errors, rather than recoverable errors.
    cfg.model_agent_cfg.vif.set_software_errs_fatal(1'b1);
    // We've loaded the binary. Run the processor to see what happens!
    super.body();
    reset_if_locked();
  endtask : body

endclass : otbn_sw_errs_fatal_chk_vseq
