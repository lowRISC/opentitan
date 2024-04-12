// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This creates the same traffic pattern as flash_ctrl_phy_arb_redun_vseq, but
// doesn't inject errors. Used to diagnose ECC errors.
class flash_ctrl_phy_arb_redun_no_fault_vseq extends flash_ctrl_err_base_vseq;
  `uvm_object_utils(flash_ctrl_phy_arb_redun_no_fault_vseq)
  `uvm_object_new

  constraint ctrl_num_c {
    ctrl_num dist { CTRL_TRANS_MIN := 2, [2:16] :/ 1};
  }

  task run_error_event();
    int delay;
    // unit 100 ns;
    delay = $urandom_range(1, 10);
    #(delay * 100ns);
    cfg.otf_scb_h.comp_off = 1;
    cfg.otf_scb_h.mem_mon_off = 1;
    `uvm_info(`gfn, "Calling collect_err_cov_status", UVM_MEDIUM)
    collect_err_cov_status(ral.fault_status);
    // host transaction unpredictably triggers err_code.mp_err.
    // Instead of checking err_code == 0, make sure hw_fault.mp_err doesn't happen.
    delay = $urandom_range(60, 90);
    #(delay * 10us);
    csr_rd_check(.ptr(ral.fault_status.mp_err), .compare_value(0));
    drain_n_finish_err_event();
  endtask
  task clean_up();
    init_controller();
  endtask // clean_up
endclass
