// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the reset_info CSR settings, and alert and cpu dump capture for random
// resets.
//
// Notice that for rstmgr both POR and scan reset have identical side-effects.
class rstmgr_reset_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_reset_vseq)

  `uvm_object_new

  constraint num_trans_c {num_trans inside {[40 : 60]};}

  constraint which_reset_c {which_reset != 0;}

  // VCS seems to have non-uniform distributions for this variable.
  rand logic   alert_enable;

  rand logic   cpu_enable;

  rand reset_e start_reset;
  constraint start_reset_c {start_reset inside {ResetPOR, ResetScan};}

  mubi4_t sw_reset_csr;

  function void post_randomize();
    if (which_reset == ResetSw) sw_reset_csr = MuBi4True;
    else sw_reset_csr = get_rand_mubi4_val(0, 2, 4);
  endfunction

  task body();
    reset_test_info_t reset_test_info;
    int expected_reset_info_code;
    logic expected_alert_enable;
    logic expected_cpu_enable;
    alert_crashdump_t expected_alert_dump = '0;
    cpu_crash_dump_t expected_cpu_dump = '0;
    alert_crashdump_t prev_alert_dump = '0;
    cpu_crash_dump_t prev_cpu_dump = '0;

    // Expect reset info to be POR when running the sequence standalone.
    if (is_running_sequence("rstmgr_reset_vseq")) begin
      check_reset_info(1, "expected reset_info to be POR");
      check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(1'b0));
    end

    `DV_CHECK_RANDOMIZE_FATAL(this)

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
      logic is_aon_reset;

      `uvm_info(`gfn, $sformatf("Starting new round %0d", i), UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      set_alert_info_for_capture(alert_dump, alert_enable);
      set_cpu_info_for_capture(cpu_dump, cpu_enable);
      csr_wr(.ptr(ral.reset_info), .value('1));

      is_aon_reset = aon_reset(which_reset);
      reset_test_info = reset_test_infos[which_reset];
      clear_enables = clear_capture_enable(which_reset);

      expected_reset_info_code = reset_test_info.code;
      expected_alert_enable = alert_enable && !clear_enables;
      expected_cpu_enable = cpu_enable && !clear_enables;
      expected_alert_dump = is_aon_reset ? '0 : (alert_enable ? alert_dump : prev_alert_dump);
      expected_cpu_dump = is_aon_reset ? '0 : (cpu_enable ? cpu_dump : prev_cpu_dump);

      `uvm_info(`gfn, $sformatf(
                "%0s with alert_en %b, cpu_en %b", which_reset.name(), alert_enable, cpu_enable),
                UVM_MEDIUM)

      send_sw_reset(sw_reset_csr);
      case (which_reset)
        ResetPOR: por_reset();
        ResetScan: send_scan_reset();
        ResetLowPower: send_reset(pwrmgr_pkg::LowPwrEntry, 0);
        ResetSw: `DV_CHECK_EQ(sw_reset_csr, MuBi4True)
        ResetHw: begin
          expected_reset_info_code = rstreqs << ral.reset_info.hw_req.get_lsb_pos();
          send_reset(pwrmgr_pkg::HwReq, rstreqs);
        end
        default: `uvm_fatal(`gfn, $sformatf("Unexpected reset type %0d", which_reset))
      endcase

      cfg.io_div4_clk_rst_vif.wait_clks(8);
      wait(cfg.rstmgr_vif.resets_o.rst_lc_n[1]);
      check_reset_info(expected_reset_info_code, reset_test_info.description);
      check_alert_info_after_reset(.alert_dump(expected_alert_dump),
                                   .enable(expected_alert_enable));
      check_cpu_info_after_reset(.cpu_dump(expected_cpu_dump), .enable(expected_cpu_enable));
      if (which_reset == ResetPOR) read_and_check_all_csrs_after_reset();
      prev_alert_dump = expected_alert_dump;
      prev_cpu_dump   = expected_cpu_dump;
    end
    csr_wr(.ptr(ral.reset_info), .value('1));
    // This clears the info registers to cancel side-effects into other sequences with stress tests.
    clear_alert_and_cpu_info();
  endtask

endclass : rstmgr_reset_vseq
