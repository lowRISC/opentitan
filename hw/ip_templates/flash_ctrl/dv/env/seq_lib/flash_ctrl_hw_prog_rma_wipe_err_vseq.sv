// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence assert erros during rma wipe stage targeting
// hit a couple of hw oriented fault_status errors.
// See 'check_status' tasks for what status errors are covered.
class flash_ctrl_hw_prog_rma_wipe_err_vseq extends flash_ctrl_err_base_vseq;
  `uvm_object_utils(flash_ctrl_hw_prog_rma_wipe_err_vseq)
  `uvm_object_new

  task run_main_event();
    logic [RmaSeedWidth-1:0] rma_seed = $urandom;
    // This test needs long rma.
    // In case en_small_rma is set for all tests,
    // force to long rma.
    send_rma_req(.rma_seed(rma_seed), .ignore_short_rma(1));
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

  endtask // run_main_event

  // fatal_std_err
  task run_error_event();
     int event_idx = $urandom_range(0, 3);

    `uvm_info(`gfn, $sformatf("event_idx :%0d", event_idx), UVM_MEDIUM)
     `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.rma_state == StRmaWordSel);,
                  , cfg.seq_cfg.state_wait_timeout_ns)
    cfg.scb_h.expected_alert["fatal_err"].expected = 1;
    cfg.scb_h.expected_alert["fatal_err"].max_delay = 2000;
    cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;

    add_glitch(event_idx);
    collect_err_cov_status(ral.fault_status);
    check_status(event_idx);
    cfg.scb_h.do_alert_check = 0;
    cfg.rma_ack_polling_stop = 1;
  endtask // run_error_event

  task add_glitch(int idx);
    string path = LIST_OF_PROG_RMA_WIPE_FORCE_PATHS[idx];
    case (idx)
      0, 1: begin
        // This will trigger std_fault_status.prog_intg_err
        // but it will be captured in the other test.
        cfg.scb_h.expected_alert["fatal_std_err"].expected = 1;
        cfg.scb_h.expected_alert["fatal_std_err"].max_delay = 2000;
        cfg.scb_h.exp_alert_contd["fatal_std_err"] = 10000;
        $assertoff(0, "tb.dut.u_flash_mp.NoReqWhenErr_A");
        flip_2bits(path);
      end
      2: begin
        `DV_CHECK(uvm_hdl_force(path, 100));
      end
      3: begin
        $assertoff(0, "tb.dut.u_flash_hw_if.ProgRdVerify_A");
        csr_wr(.ptr(ral.prog_type_en.normal), .value(0));
      end
      default: `uvm_error(`gfn, $sformatf("unsupported index %0d", idx))
    endcase // case (idx)
    cfg.clk_rst_vif.wait_clks(10);

    // Since idx = 3 doesn't use force, exclude it from release.
    if (idx != 3) begin
      `DV_CHECK(uvm_hdl_release(path));
    end
  endtask

  task check_status(int idx);
    uvm_object fld;
    case (idx)
      0: begin
        fld = ral.fault_status.prog_err;
      end
      1: begin
        fld = ral.fault_status.mp_err;
      end
      2: begin
        fld = ral.fault_status.prog_win_err;
      end
      3: begin
        fld = ral.fault_status.prog_type_err;
      end
      default: `uvm_error(`gfn, $sformatf("unsupported index %0d", idx))
    endcase
    csr_rd_check(.ptr(ral.err_code), .compare_value(0));
    csr_rd_check(.ptr(fld), .compare_value(1));
  endtask // check_status

  task clean_up();
    cfg.otf_scb_h.stop = 1;
    cfg.otf_scb_h.clear_fifos();
    apply_reset();
  endtask // clean_up
endclass // flash_ctrl_hw_prog_rma_wipe_err_vseq
