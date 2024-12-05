// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the reset_info CSR settings, and alert and cpu dump capture for random
// resets.
//
// Notice that for rstmgr both POR and scan reset have identical side-effects.
class rstmgr_reset_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_reset_vseq)

  `uvm_object_new

  typedef bit [ResetLast-1:0] which_resets_t;

  rand bit por_rst;
  rand bit scan_rst;
  rand bit low_power_rst;
  rand bit sw_rst;
  rand bit hw_rst;

  constraint which_resets_c {
    $onehot(
        {por_rst, scan_rst, low_power_rst, sw_rst || hw_rst}
    );
  }

  constraint num_trans_c {num_trans inside {[40 : 60]};}

  // VCS seems to have non-uniform distributions for this variable.
  rand logic   alert_enable;

  rand logic   cpu_enable;

  rand reset_e start_reset;
  constraint start_reset_c {start_reset inside {ResetPOR, ResetScan};}

  which_resets_t which_resets;
  mubi4_t sw_reset_csr;

  function which_resets_t create_which_resets();
    which_resets_t which_resets;
    if (por_rst) which_resets[ResetPOR] = 1;
    if (scan_rst) which_resets[ResetScan] = 1;
    if (low_power_rst) which_resets[ResetLowPower] = 1;
    if (sw_rst) which_resets[ResetSw] = 1;
    if (hw_rst) which_resets[ResetHw] = 1;
    return which_resets;
  endfunction

  function bit has_aon_reset(which_resets_t which_resets);
    return which_resets[ResetPOR] || which_resets[ResetScan];
  endfunction

  function bit clear_capture_enable(which_resets_t which_resets);
    return (which_resets & ~(1 << ResetLowPower)) ? 1 : 0;
  endfunction

  function void post_randomize();
    sw_reset_csr = get_rand_mubi4_val(0, 2, 4);
  endfunction

  function string resets_description(which_resets_t which_resets, rstreqs_t rstreqs);
    string msg = "Resets to be sent:";
    bit some;
    for (reset_e r = r.first(); r != r.last(); r = r.next()) begin
      if (which_resets[r]) begin
        if (some) msg = {msg, ", "};
        msg = {msg, " ", reset_name[r]};
        if (r == ResetHw) msg = {msg, $sformatf(" with 0x%x", rstreqs)};
        some = 1;
      end
    end
    return msg;
  endfunction

  function reset_info_t get_expected_reset_info(which_resets_t which_resets, rstreqs_t rstreqs);
    reset_info_t reset_info;
    for (reset_e r = r.first(); r != r.last(); r = r.next()) begin
      if (which_resets[r]) reset_info |= get_reset_code(r, rstreqs);
    end
    return reset_info;
  endfunction

  task body();
    reset_info_t expected_reset_info_code;
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

    cfg.clk_rst_vif.wait_clks(8);
    // Wait till rst_lc_n is inactive for non-aon.
    `DV_WAIT(cfg.rstmgr_vif.resets_o.rst_lc_n[1])

    check_reset_info(get_reset_code(start_reset, 0), {reset_name[start_reset], " reset"});
    check_alert_info_after_reset(expected_alert_dump, expected_alert_enable);
    check_cpu_info_after_reset(expected_cpu_dump, expected_cpu_enable);
    prev_alert_dump = expected_alert_dump;
    prev_cpu_dump   = expected_cpu_dump;

    for (int i = 0; i < num_trans; ++i) begin : trans_loop
      logic clear_enables;
      logic has_aon;

      `uvm_info(`gfn, $sformatf("Starting new round %0d", i), UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      which_resets = create_which_resets();
      set_alert_info_for_capture(alert_dump, alert_enable);
      set_cpu_info_for_capture(cpu_dump, cpu_enable);
      csr_wr(.ptr(ral.reset_info), .value('1));
      if (which_resets[ResetSw]) begin
        sw_reset_csr = MuBi4True;
        csr_wr(.ptr(ral.reset_req), .value(sw_reset_csr));
      end
      has_aon = has_aon_reset(which_resets);
      clear_enables = clear_capture_enable(which_resets);

      `uvm_info(`gfn, $sformatf("Expected to %0s capture enables", clear_enables ? "clear" : "hold"
                ), UVM_MEDIUM)
      expected_reset_info_code = get_expected_reset_info(which_resets, rstreqs);
      expected_alert_enable = alert_enable && !clear_enables;
      expected_cpu_enable = cpu_enable && !clear_enables;
      expected_alert_dump = has_aon ? '0 : (alert_enable ? alert_dump : prev_alert_dump);
      expected_cpu_dump = has_aon ? '0 : (cpu_enable ? cpu_dump : prev_cpu_dump);
      `uvm_info(`gfn, resets_description(which_resets, rstreqs), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("resets with alert_en %b, cpu_en %b", alert_enable, cpu_enable),
                UVM_MEDIUM)

      fork
        if (which_resets[ResetPOR]) por_reset(.complete_it(0));
        if (which_resets[ResetScan]) send_scan_reset(.complete_it(0));
        if (which_resets[ResetLowPower]) begin
          cfg.io_div4_clk_rst_vif.wait_clks(lowpower_rst_cycles);
          send_lowpower_reset(.complete_it(0));
        end
        if (which_resets[ResetSw]) begin
          cfg.io_div4_clk_rst_vif.wait_clks(sw_rst_cycles);
          send_sw_reset(.complete_it(0));
        end
        if (which_resets[ResetHw]) begin
          cfg.io_div4_clk_rst_vif.wait_clks(hw_rst_cycles);
          send_hw_reset(rstreqs, .complete_it(0));
        end
      join
      #(reset_us * 1us);
      reset_done();

      cfg.io_div4_clk_rst_vif.wait_clks(8);
      wait(cfg.rstmgr_vif.resets_o.rst_lc_n[1]);
      check_reset_info(expected_reset_info_code);
      check_alert_info_after_reset(.alert_dump(expected_alert_dump),
                                   .enable(expected_alert_enable));
      check_cpu_info_after_reset(.cpu_dump(expected_cpu_dump), .enable(expected_cpu_enable));
      if (has_aon) read_and_check_all_csrs_after_reset();
      prev_alert_dump = expected_alert_dump;
      prev_cpu_dump   = expected_cpu_dump;
    end : trans_loop
    csr_wr(.ptr(ral.reset_info), .value('1));
    // This clears the info registers to cancel side-effects into other sequences with stress tests.
    clear_alert_and_cpu_info();
  endtask : body

endclass : rstmgr_reset_vseq
