// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_phy_arb_redun_vseq extends flash_ctrl_err_base_vseq;
  `uvm_object_utils(flash_ctrl_phy_arb_redun_vseq)
  `uvm_object_new

  constraint ctrl_num_c {
    ctrl_num dist { CTRL_TRANS_MIN := 2, [2:16] :/ 1};
  }

  task run_error_event();
    int delay;
    string path = {"tb.dut.u_eflash.gen_flash_cores[0].",
                   "u_core.u_host_arb.gen_input_bufs[1].u_req_buf.out_o[1:0]"};
    cfg.scb_h.expected_alert["fatal_err"].expected = 1;
    cfg.scb_h.expected_alert["fatal_err"].max_delay = cfg.seq_cfg.long_fatal_err_delay;
    cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;

    // unit 100 ns;
    delay = $urandom_range(1, 10);
    #(delay * 100ns);
    cfg.otf_scb_h.comp_off = 1;
    cfg.otf_scb_h.mem_mon_off = 1;

    `DV_CHECK(uvm_hdl_force(path, 2'h0))

    delay = $urandom_range(5, 10);
    #(delay * 10us);
    `DV_CHECK(uvm_hdl_release(path))
    check_fault(ral.fault_status.arb_err);
    collect_err_cov_status(ral.fault_status);
    // host transaction unpredictably triggers err_code.mp_err.
    // In stead of checking err_code == 0, make sure hw_fault.mp_err doesn't happen.
    csr_rd_check(.ptr(ral.fault_status.mp_err), .compare_value(0));
    drain_n_finish_err_event();
  endtask
  task clean_up();
    init_controller();
  endtask // clean_up
endclass
