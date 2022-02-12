// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the reset_info CSR settings for random resets.
// Notice as far as rstmgr once POR or scan reset are asserted, they have
// identical side-effects for rstmgr.
//
// Each run releases rst_cpu_n a few cycles after a scan reset. This requires
// the responder to be disabled from automatically deactivating rst_cpu_n after
// rst_sys_src_n goes inactive.
//
// It is simpler to manipulate the responder once running so we cause a scan
// reset after disabling it, and before the other resets. This tests that resets
// other than scan don't update the reset_info CSR, and don't capture cpu or
// alert dumps.
class rstmgr_reset_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_reset_vseq)

  `uvm_object_new

  rand logic enable_alert_info;
  rand logic enable_cpu_info;

  rand int   wait_for_release_response_update_cycles;
  constraint wait_for_release_response_update_cycles_c {
    wait_for_release_response_update_cycles inside {[4 : 12]};
  }

  rand int rand_trans_before_enabling_cpu_rst_response;
  constraint rand_trans_before_enabling_cpu_rst_response_c {
    rand_trans_before_enabling_cpu_rst_response >= 0;
    rand_trans_before_enabling_cpu_rst_response < 4;
  }

  rand reset_e start_reset;
  constraint start_reset_c {start_reset inside {ResetPOR, ResetScan};}

  local task update_cpu_to_sys_rst_release_response(bit enable);
    enable_cpu_to_sys_rst_release_response = enable;
    `uvm_info(`gfn, $sformatf("%0sabling sys_rst_responder", enable ? "En" : "Dis"), UVM_MEDIUM)
    // Wait a small number of cycles for this to take effect.
    // If wait too little capture may be unpredictable.
    cfg.clk_rst_vif.wait_clks(wait_for_release_response_update_cycles);
  endtask

  // Disable automatic deassertion of rst_cpu_n when running standalone,
  // in order to test info capture.
  task pre_start();
    super.pre_start();
    `uvm_info(`gfn, "In pre_start", UVM_MEDIUM)
    update_cpu_to_sys_rst_release_response(.enable(0));
  endtask

  task body();
    reset_test_info_t reset_test_info;
    int expected_reset_info_code;
    logic expected_alert_enable;
    logic expected_cpu_enable;
    alert_pkg::alert_crashdump_t prev_alert_dump = '0;
    ibex_pkg::crash_dump_t prev_cpu_dump = '0;
    int trans_before_enabling_cpu_rst_response;
    bit capture = 0;

    // Expect reset info to be POR when running the sequence standalone.
    if (is_running_sequence("rstmgr_reset_vseq")) begin
      check_reset_info(1, "expected reset_info to be POR");
      check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(1'b0));
    end

    `DV_CHECK_RANDOMIZE_FATAL(this)

    // Run with cpu_rst_response disabled for a few cycles to make sure no capture happens
    // until rst_cpu_n is inactive.
    trans_before_enabling_cpu_rst_response = rand_trans_before_enabling_cpu_rst_response;
    `uvm_info(`gfn, $sformatf(
              "Will wait for %0d resets before enabling rst_cpu_n response",
              trans_before_enabling_cpu_rst_response
              ), UVM_MEDIUM)

    // Clear reset_info register, and enable cpu and alert info capture.
    set_alert_info_for_capture(alert_dump, enable_alert_info);
    set_cpu_info_for_capture(cpu_dump, enable_cpu_info);
    csr_wr(.ptr(ral.reset_info), .value('1));

    // We need to start with an AON reset to process non-capturing resets.
    if (start_reset == ResetPOR) por_reset();
    else if (start_reset == ResetScan) send_scan_reset();

    reset_test_info = reset_test_infos[start_reset];
    cfg.clk_rst_vif.wait_clks(8);
    // Wait till rst_lc_n is inactive for non-aon.
    wait(cfg.rstmgr_vif.resets_o.rst_lc_n[1]);

    check_reset_info(reset_test_info.expects.code, reset_test_info.description);
    check_alert_info_after_reset('0, 0);
    check_cpu_info_after_reset('0, 0);

    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, $sformatf("Starting new round %0d", i), UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      set_alert_info_for_capture(alert_dump, enable_alert_info);
      set_cpu_info_for_capture(cpu_dump, enable_cpu_info);
      csr_wr(.ptr(ral.reset_info), .value('1));
      reset_test_info = reset_test_infos[which_reset];

      if (i == trans_before_enabling_cpu_rst_response) begin
        update_cpu_to_sys_rst_release_response(.enable(1));
        capture = 1;
      end
      expected_reset_info_code = reset_test_info.expects.code;
      expected_alert_enable = enable_alert_info && (!capture || reset_test_info.expects.enable);
      expected_cpu_enable = enable_cpu_info && (!capture || reset_test_info.expects.enable);

      case (which_reset)
        ResetPOR, ResetScan: begin
          // This resets the info registers, which means the previous info contents become zero.
          prev_alert_dump = '0;
          prev_cpu_dump = '0;
          expected_alert_enable = 0;
          expected_cpu_enable = 0;
          if (which_reset == ResetPOR) por_reset();
          else if (which_reset == ResetScan) send_scan_reset();
        end
        ResetLowPower: send_reset(pwrmgr_pkg::LowPwrEntry, 0);
        ResetNdm: send_ndm_reset();
        ResetSw: send_sw_reset();
        ResetHw: begin
          expected_reset_info_code = {'0, rstreqs, 4'b0};
          send_reset(pwrmgr_pkg::HwReq, rstreqs);
        end
        default: `uvm_fatal(`gfn, $sformatf("Unexpected reset type %0d", which_reset))
      endcase

      cfg.clk_rst_vif.wait_clks(8);
      wait(cfg.rstmgr_vif.resets_o.rst_lc_n[1]);
      if (!capture) begin
        `uvm_info(`gfn, $sformatf("In no capture %0d", i), UVM_MEDIUM)
        check_reset_info(which_reset inside {ResetPOR, ResetScan} ? expected_reset_info_code : 0,
                         reset_test_info.description);
        check_alert_info_after_reset(.alert_dump('0), .enable(expected_alert_enable));
        check_cpu_info_after_reset(.cpu_dump('0), .enable(expected_cpu_enable));
      end else begin
        `uvm_info(`gfn, $sformatf("In capture %0d", i), UVM_MEDIUM)
        check_reset_info(expected_reset_info_code, reset_test_info.description);

        if (reset_test_info.expects.update && enable_alert_info) begin
          check_alert_info_after_reset(alert_dump, expected_alert_enable);
          prev_alert_dump = alert_dump;
        end else begin
          check_alert_info_after_reset(prev_alert_dump, expected_alert_enable);
        end

        if (reset_test_info.expects.update && enable_cpu_info) begin
          check_cpu_info_after_reset(cpu_dump, expected_cpu_enable);
          prev_cpu_dump = cpu_dump;
        end else begin
          check_cpu_info_after_reset(prev_cpu_dump, expected_cpu_enable);
        end
      end
    end
    csr_wr(.ptr(ral.reset_info), .value('1));
    // This clears the info registers to cancel side-effects into other sequences with stress tests.
    update_cpu_to_sys_rst_release_response(.enable(1));
    clear_alert_and_cpu_info();
  endtask

endclass : rstmgr_reset_vseq
