// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the reset_info CSR settings, and alert and cpu dump capture for random
// resets.
//
// Notice that for rstmgr both POR and scan reset have identical side-effects.
//
// Each run releases rst_cpu_n a few cycles after a scan reset. This requires
// the responder to be disabled from automatically deactivating rst_cpu_n after
// rst_sys_src_n goes inactive.
//
// It is simpler to manipulate the responder once running so we cause another
// aon reset after disabling it, and before the other resets. This tests that,
// prior to rst_cpu_n, non-aon resets don't update the reset_info CSR, and don't
// capture cpu or alert dumps.
class rstmgr_reset_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_reset_vseq)

  `uvm_object_new

  constraint num_trans_c {num_trans inside {[40 : 60]};}

  constraint which_reset_c {which_reset != 0;}

  // VCS seems to have non-uniform distributions for this variable.
  rand logic alert_enable;

  rand logic cpu_enable;

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

  mubi4_t sw_reset_csr;

  function void post_randomize();
    if (which_reset == ResetSw) sw_reset_csr = MuBi4True;
    else sw_reset_csr = get_rand_mubi4_val(0, 2, 4);
  endfunction

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
    alert_crashdump_t expected_alert_dump = '0;
    cpu_crash_dump_t expected_cpu_dump = '0;
    alert_crashdump_t prev_alert_dump = '0;
    cpu_crash_dump_t prev_cpu_dump = '0;
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
    set_alert_info_for_capture(alert_dump, alert_enable);
    set_cpu_info_for_capture(cpu_dump, cpu_enable);
    csr_wr(.ptr(ral.reset_info), .value('1));

    // We need to start with an AON reset to process non-capturing resets.
    if (start_reset == ResetPOR) por_reset();
    else if (start_reset == ResetScan) send_scan_reset();

    // On either of these resets we expect captures to be all zero and enables to be off.
    expected_alert_dump = '0;
    expected_cpu_dump = '0;
    expected_alert_enable = 0;
    expected_cpu_enable = 0;

    reset_test_info = reset_test_infos[start_reset];
    cfg.clk_rst_vif.wait_clks(8);
    // Wait till rst_lc_n is inactive for non-aon.
    wait(cfg.rstmgr_vif.resets_o.rst_lc_n[1]);

    check_reset_info(reset_test_info.code, reset_test_info.description);
    check_alert_info_after_reset(expected_alert_dump, expected_alert_enable);
    check_cpu_info_after_reset(expected_cpu_dump, expected_cpu_enable);
    prev_alert_dump = expected_alert_dump;
    prev_cpu_dump   = expected_cpu_dump;

    for (int i = 0; i < num_trans; ++i) begin
      logic clear_enables;
      logic update_capture_dump;

      `uvm_info(`gfn, $sformatf("Starting new round %0d", i), UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      if (i == trans_before_enabling_cpu_rst_response) begin
        update_cpu_to_sys_rst_release_response(.enable(1));
        capture = 1;
      end

      set_alert_info_for_capture(alert_dump, alert_enable);
      set_cpu_info_for_capture(cpu_dump, cpu_enable);
      csr_wr(.ptr(ral.reset_info), .value('1));

      reset_test_info = reset_test_infos[which_reset];
      clear_enables = aon_reset(which_reset) || (capture && clear_capture_enable(which_reset));
      update_capture_dump = capture && !aon_reset(which_reset);

      expected_reset_info_code = (capture || aon_reset(which_reset)) ? reset_test_info.code : '0;
      expected_alert_enable = alert_enable && !clear_enables;
      expected_cpu_enable = cpu_enable && !clear_enables;
      // This is expedient, since aon resets will clear any dumps.
      if (aon_reset(which_reset)) begin
        prev_alert_dump = '0;
        prev_cpu_dump   = '0;
      end
      expected_alert_dump = (alert_enable && update_capture_dump) ? alert_dump : prev_alert_dump;
      expected_cpu_dump   = (cpu_enable && update_capture_dump) ? cpu_dump : prev_cpu_dump;

      `uvm_info(`gfn, $sformatf(
                "%0s with global capturing %0sbled, alert_en %b, cpu_en %b",
                which_reset.name(),
                (capture ? "en" : "dis"),
                alert_enable,
                cpu_enable
                ), UVM_MEDIUM)

      send_sw_reset(sw_reset_csr);
      case (which_reset)
        ResetPOR: por_reset();
        ResetScan: send_scan_reset();
        ResetLowPower: send_reset(pwrmgr_pkg::LowPwrEntry, 0);
        ResetNdm: send_ndm_reset();
        ResetSw: `DV_CHECK_EQ(sw_reset_csr, MuBi4True)
        ResetHw: begin
          if (capture) expected_reset_info_code = {'0, rstreqs, 4'b0};
          send_reset(pwrmgr_pkg::HwReq, rstreqs);
        end
        default: `uvm_fatal(`gfn, $sformatf("Unexpected reset type %0d", which_reset))
      endcase

      cfg.clk_rst_vif.wait_clks(8);
      wait(cfg.rstmgr_vif.resets_o.rst_lc_n[1]);
      check_reset_info(expected_reset_info_code, reset_test_info.description);
      check_alert_info_after_reset(.alert_dump(expected_alert_dump),
                                   .enable(expected_alert_enable));
      check_cpu_info_after_reset(.cpu_dump(expected_cpu_dump), .enable(expected_cpu_enable));
      if (capture) begin
        prev_alert_dump = expected_alert_dump;
        prev_cpu_dump   = expected_cpu_dump;
      end
    end
    csr_wr(.ptr(ral.reset_info), .value('1));
    // This clears the info registers to cancel side-effects into other sequences with stress tests.
    update_cpu_to_sys_rst_release_response(.enable(1));
    clear_alert_and_cpu_info();
  endtask

endclass : rstmgr_reset_vseq
