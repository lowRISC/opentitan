// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_common_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  // in run_tl_intg_err_vseq, csr_rw seq is running in the parallel. And intg error will be injected
  // which may affect fatal_alert_cause.integrity_error. Exclude checking it
  virtual function void apply_extra_excl_for_tl_intg_vseq();
    cfg.ral.csr_excl.add_excl(ral.fatal_alert_cause.integrity_error.`gfn,
                              CsrExclCheck, CsrNonInitTests);
  endfunction

endclass
