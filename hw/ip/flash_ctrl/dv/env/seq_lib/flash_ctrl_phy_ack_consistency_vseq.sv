// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test triggers tb.dut.u_eflash.gen_flash_cores[0].u_core.spurious_ack_o
// by force.
class flash_ctrl_phy_ack_consistency_vseq extends flash_ctrl_phy_host_grant_err_vseq;
  `uvm_object_utils(flash_ctrl_phy_ack_consistency_vseq)
  `uvm_object_new

  task run_error_event();
    int delay;
    bit add_err1, add_err2;
    string path1 = "tb.dut.u_eflash.gen_flash_cores[0].u_core.ctrl_rsp_vld";
    string path2 = "tb.dut.u_eflash.gen_flash_cores[0].u_core.host_req_done_o";

    // Once error event is triggered, corrupted data propagate all the way down to flash phy interface and terminated.
    // This can causes unexpected errors.
    // Therefore, ignore potential unexpected err and check
    // expected error only.
    cfg.scb_h.skip_alert_chk["recov_err"] = 1;

    cfg.scb_h.expected_alert["fatal_err"].expected = 1;
    cfg.scb_h.expected_alert["fatal_err"].max_delay = 20000;
    cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;
    $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[0].u_host_rsp_fifo.gen_normal_fifo.u_fifo_cnt");

    repeat (2) begin
      // unit 100 ns;
      delay = $urandom_range(1, 10);
      #(delay * 100ns);

      if (add_err1) begin
        `DV_CHECK(uvm_hdl_release(path1))
      end
      if (add_err2) begin
        `DV_CHECK(uvm_hdl_release(path2))
      end

      if (add_err1 == 0 && add_err2 == 0) begin
        $assertoff(0, "tb.dut.u_flash_mp.NoReqWhenErr_A");
        randcase
          1: begin
            // This error injection can cause catastrophic event
            // Set fatal_std_err and stop tl response check
            cfg.scb_h.expected_alert["fatal_std_err"].expected = 1;
            cfg.scb_h.expected_alert["fatal_std_err"].max_delay = 20000;
            cfg.scb_h.exp_alert_contd["fatal_std_err"] = 10000;
            cfg.scb_h.stop_tl_err_chk = 1;
            cfg.m_tl_agent_cfg.check_tl_errs = 0;
            add_err1 = 1;
            @(posedge cfg.flash_ctrl_vif.ctrl_fsm_idle);
            `DV_CHECK(uvm_hdl_force(path1, 1))
          end
          1: begin
            add_err2 = 1;
            wait(cfg.flash_ctrl_vif.host_outstanding == 0);
            `DV_CHECK(uvm_hdl_force(path2, 1))
          end
        endcase // randcase
        cfg.otf_scb_h.comp_off = 1;
        cfg.otf_scb_h.mem_mon_off = 1;
      end
    end // repeat (2)
    check_fault(ral.fault_status.spurious_ack);
    collect_err_cov_status(ral.fault_status);
    // sw error can be unpredictably triggered. (err_code.prog_err)
    // In stead of checking err_code == 0,
    // make sure hw_fault.prog_err doesn't happen.
    csr_rd_check(.ptr(ral.fault_status.prog_err), .compare_value(0));
    drain_n_finish_err_event();
  endtask
endclass
