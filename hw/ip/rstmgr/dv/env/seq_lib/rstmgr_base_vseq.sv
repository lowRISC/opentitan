// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rstmgr_base_vseq extends cip_base_vseq #(
  .RAL_T              (rstmgr_reg_block),
  .CFG_T              (rstmgr_env_cfg),
  .COV_T              (rstmgr_env_cov),
  .VIRTUAL_SEQUENCER_T(rstmgr_virtual_sequencer)
);

  `uvm_object_utils(rstmgr_base_vseq)

  // Set clock frequencies per spec, except the aon is 200kHZ, which is
  // too slow and could slow testing down for no good reason.
  localparam int AON_FREQ_MHZ = 3;
  localparam int IO_FREQ_MHZ = 96;
  localparam int IO_DIV2_FREQ_MHZ = 48;
  localparam int IO_DIV4_FREQ_MHZ = 24;
  localparam int MAIN_FREQ_MHZ = 100;
  localparam int USB_FREQ_MHZ = 48;

  // POR needs to be stable not less than 32 clock cycles, plus some extra, before it
  // propagates to the rest of the logic.
  localparam int POR_CLK_CYCLES = 40;

  // This is only used for the various clocks to start ticking, so can be any small number.
  localparam int BOGUS_RESET_CLK_CYCLES = 2;

  // Some extra cycles from reset going inactive before the CPU's reset goes inactive.
  localparam int CPU_RESET_CLK_CYCLES = 10;

  rand logic                                sw_reset;
  rand logic                                scan_reset;
  rand logic                                low_power_reset;
  rand logic                                ndm_reset;

  rand sw_rst_t                             sw_rst_regwen;
  rand sw_rst_t                             sw_rst_ctrl_n;

  bit                                       reset_once;

  rand ibex_pkg::crash_dump_t               cpu_dump;
  rand alert_pkg::alert_crashdump_t         alert_dump;

  rand logic [pwrmgr_pkg::HwResetWidth-1:0] rstreqs;

  rand logic                                scan_rst_ni;
  constraint scan_rst_ni_c {scan_rst_ni == 1;}

  rand int rst_to_req_cycles;
  constraint rst_to_req_cycles_c {rst_to_req_cycles inside {[1 : 6]};}

  rand int scanmode_to_scan_rst_cycles;
  constraint scanmode_to_scan_rst_cycles_c {scanmode_to_scan_rst_cycles inside {[0 : 4]};}

  rand int ndm_reset_cycles;
  constraint ndm_reset_cycles_c {ndm_reset_cycles inside {[4 : 16]};}

  rand int non_ndm_reset_cycles;
  constraint non_ndm_reset_cycles_c {non_ndm_reset_cycles inside {[4 : 16]};}

  // various knobs to enable certain routines
  bit     do_rstmgr_init     = 1'b1;

  mubi4_t scanmode;
  int     scanmode_on_weight = 8;

  `uvm_object_new

  function void post_randomize();
    scanmode = get_rand_mubi4_val(scanmode_on_weight, 4, 4);
  endfunction

  function void update_scanmode(prim_mubi_pkg::mubi4_t value);
    cfg.rstmgr_vif.scanmode_i = value;
  endfunction

  function void update_scan_rst_n(logic value);
    cfg.rstmgr_vif.scan_rst_ni = value;
  endfunction

  function void set_pwrmgr_rst_reqs(logic rst_lc_req, logic rst_sys_req);
    `uvm_info(`gfn, $sformatf("Setting pwr_i lc_req=%x sys_req=%x", rst_lc_req, rst_sys_req),
              UVM_MEDIUM)
    cfg.rstmgr_vif.pwr_i.rst_lc_req  = {rstmgr_pkg::PowerDomains{rst_lc_req}};
    cfg.rstmgr_vif.pwr_i.rst_sys_req = {rstmgr_pkg::PowerDomains{rst_sys_req}};
  endfunction

  function void set_rstreqs(logic [pwrmgr_pkg::HwResetWidth:0] rstreqs);
    cfg.rstmgr_vif.pwr_i.rstreqs = rstreqs;
  endfunction

  function void set_reset_cause(pwrmgr_pkg::reset_cause_e reset_cause);
    cfg.rstmgr_vif.pwr_i.reset_cause = reset_cause;
  endfunction

  function void set_ndmreset_req(logic value);
    cfg.rstmgr_vif.cpu_i.ndmreset_req = value;
  endfunction

  function void set_rst_cpu_n(logic value);
    cfg.rstmgr_vif.cpu_i.rst_cpu_n = value;
  endfunction

  function logic is_running_sequence(string seq_name);
    string actual_sequence = "none";
    // Okay to ignore return value since the default won't match.
    void'($value$plusargs("UVM_TEST_SEQ=%0s", actual_sequence));
    return actual_sequence.compare(seq_name) == 0;
  endfunction

  task check_reset_info(logic [TL_DW-1:0] expected_value, string msg = "reset_info mismatch");
    csr_rd_check(.ptr(ral.reset_info), .compare_value(expected_value), .err_msg(msg));
  endtask

  function void set_cpu_dump_info(ibex_pkg::crash_dump_t cpu_dump);
    `uvm_info(`gfn, $sformatf("Setting cpu_dump_i to %p", cpu_dump), UVM_MEDIUM)
    cfg.rstmgr_vif.cpu_dump_i = cpu_dump;
  endfunction

  task check_cpu_dump_info(ibex_pkg::crash_dump_t cpu_dump);
    `uvm_info(`gfn, "Checking cpu_info", UVM_MEDIUM)
    csr_wr(.ptr(ral.cpu_info_ctrl.index), .value(3));
    csr_rd_check(.ptr(ral.cpu_info), .compare_value(cpu_dump.current_pc),
                 .err_msg("checking current_pc"));
    csr_wr(.ptr(ral.cpu_info_ctrl.index), .value(2));
    csr_rd_check(.ptr(ral.cpu_info), .compare_value(cpu_dump.next_pc),
                 .err_msg("checking next_pc"));
    csr_wr(.ptr(ral.cpu_info_ctrl.index), .value(1));
    csr_rd_check(.ptr(ral.cpu_info), .compare_value(cpu_dump.last_data_addr),
                 .err_msg("checking last_data_addr"));
    csr_wr(.ptr(ral.cpu_info_ctrl.index), .value(0));
    csr_rd_check(.ptr(ral.cpu_info), .compare_value(cpu_dump.exception_addr),
                 .err_msg("checking exception_addr"));
  endtask

  function void set_alert_dump_info(alert_pkg::alert_crashdump_t alert_dump);
    `uvm_info(`gfn, $sformatf(
              "Setting alert_dump_i to 0x%x", linearized_alert_dump_t'({>>{alert_dump}})),
              UVM_MEDIUM)
    cfg.rstmgr_vif.alert_dump_i = alert_dump;
  endfunction

  task check_alert_dump_info(alert_pkg::alert_crashdump_t alert_dump);
    localparam int DumpWidth = $bits(alert_dump);
    localparam int WordWidth = 32;
    logic [DumpWidth-1:0] linear_dump = {>>{alert_dump}};
    int                   i;
    `uvm_info(`gfn, "Checking alert_info", UVM_MEDIUM)
    for (i = 0; i + WordWidth <= DumpWidth; i += WordWidth) begin
      csr_wr(.ptr(ral.alert_info_ctrl.index), .value(i / WordWidth));
      csr_rd_check(.ptr(ral.alert_info), .compare_value(linear_dump[i+:WordWidth]),
                   .err_msg($sformatf("checking alert_info bits %0d:%0d", i + 31, i)));
    end
    if (i < DumpWidth) begin
      logic [(DumpWidth % 32) - 1:0] word = linear_dump >> i;
      csr_wr(.ptr(ral.alert_info_ctrl.index), .value(i / WordWidth));
      csr_rd_check(.ptr(ral.alert_info), .compare_value(word),
                   .err_msg($sformatf("checking alert_info bits %0d:%0d", DumpWidth - 1, i)));
    end
  endtask

  task set_alert_info_for_capture(alert_pkg::alert_crashdump_t alert_dump, logic enable);
    set_alert_dump_info(alert_dump);
    `uvm_info(`gfn, $sformatf("%0sabling alert_info capture", (enable ? "En" : "Dis")), UVM_MEDIUM)
    csr_wr(.ptr(ral.alert_info_ctrl.en), .value(enable));
  endtask

  task set_cpu_info_for_capture(ibex_pkg::crash_dump_t cpu_dump, logic enable);
    set_cpu_dump_info(cpu_dump);
    `uvm_info(`gfn, $sformatf("%0sabling cpu_info capture", (enable ? "En" : "Dis")), UVM_MEDIUM)
    csr_wr(.ptr(ral.cpu_info_ctrl.en), .value(enable));
  endtask

  task set_alert_and_cpu_info_for_capture(alert_pkg::alert_crashdump_t alert_dump,
                                          ibex_pkg::crash_dump_t cpu_dump);
    set_alert_info_for_capture(alert_dump, 1'b1);
    set_cpu_info_for_capture(cpu_dump, 1'b1);
  endtask

  task check_alert_info_after_reset(alert_pkg::alert_crashdump_t alert_dump, logic enable);
    csr_rd_check(.ptr(ral.alert_info_ctrl.en), .compare_value(enable),
                 .err_msg($sformatf("Expected alert info capture enable %b", enable)));
    csr_wr(.ptr(ral.alert_info_ctrl.en), .value(enable));
    check_alert_dump_info(alert_dump);
  endtask

  task check_cpu_info_after_reset(ibex_pkg::crash_dump_t cpu_dump, logic enable);
    csr_rd_check(.ptr(ral.cpu_info_ctrl.en), .compare_value(enable),
                 .err_msg($sformatf("Expected cpu info capture enable %b", enable)));
    csr_wr(.ptr(ral.cpu_info_ctrl.en), .value(enable));
    check_cpu_dump_info(cpu_dump);
  endtask

  // Checks both alert and cpu_info_ctrl.en, and their _info contents.
  // This is tricky: both ctrl.en fields don't necessarily match the mirrored value since the
  // hardware may update them on most resets. This can cause the subsequent writes to the .index
  // field to overwrite the .en field. To make things simpler, after checking .en's expected
  // value we write it to update the mirrored value.
  task check_alert_and_cpu_info_after_reset(alert_pkg::alert_crashdump_t alert_dump,
                                            ibex_pkg::crash_dump_t cpu_dump, logic enable);
    check_alert_info_after_reset(alert_dump, enable);
    check_cpu_info_after_reset(cpu_dump, enable);
  endtask

  task clear_alert_and_cpu_info();
    set_alert_and_cpu_info_for_capture('0, '0);
    send_sw_reset();
    check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(0));
  endtask

  task clear_sw_rst_ctrl_n();
    const sw_rst_t sw_rst_all_ones = '1;
    csr_wr(.ptr(ral.sw_rst_ctrl_n[0]), .value(sw_rst_all_ones));
    csr_rd_check(.ptr(ral.sw_rst_ctrl_n[0]), .compare_value(sw_rst_all_ones),
                 .err_msg("Expected sw_rst_ctrl_n to be set"));
  endtask

  // Stimulate and check sw_rst_ctrl_n with a given sw_rst_regen setting.
  task check_sw_rst_ctrl_n(sw_rst_t sw_rst_ctrl_n, sw_rst_t sw_rst_regen, bit erase_ctrl_n);
    sw_rst_t exp_ctrl_n;

    `uvm_info(`gfn, $sformatf("Set sw_rst_ctrl_n to 0x%0x", sw_rst_ctrl_n), UVM_MEDIUM)
    csr_wr(.ptr(ral.sw_rst_ctrl_n[0]), .value(sw_rst_ctrl_n));
    // And check that the reset outputs match the actual ctrl_n settings.
    // Allow for domain crossing delay.
    cfg.io_div2_clk_rst_vif.wait_clks(3);
    exp_ctrl_n = ~sw_rst_regen | sw_rst_ctrl_n;
    `uvm_info(`gfn, $sformatf(
              "regen=%b, ctrl_n=%b, expected=%b", sw_rst_regen, sw_rst_ctrl_n, exp_ctrl_n),
              UVM_MEDIUM)
    csr_rd_check(.ptr(ral.sw_rst_ctrl_n[0]), .compare_value(exp_ctrl_n),
                 .err_msg("Expected enabled updates in sw_rst_ctrl_n"));
    if (erase_ctrl_n) clear_sw_rst_ctrl_n();
  endtask

  // Happens with hardware resets.
  local task reset_start(pwrmgr_pkg::reset_cause_e reset_cause);
    set_reset_cause(reset_cause);
    // These lag the reset requests since they are set after the pwrmgr fast fsm has made some
    // state transitions.
    cfg.io_div4_clk_rst_vif.wait_clks(rst_to_req_cycles);
    set_pwrmgr_rst_reqs(.rst_lc_req('1), .rst_sys_req('1));
  endtask

  local task reset_done();
    set_reset_cause(pwrmgr_pkg::ResetNone);
    set_pwrmgr_rst_reqs(.rst_lc_req('0), .rst_sys_req('0));
  endtask

  task release_reset(pwrmgr_pkg::reset_cause_e reset_cause);
    cfg.io_div4_clk_rst_vif.wait_clks(non_ndm_reset_cycles);
    // Cause the reset to drop.
    `uvm_info(`gfn, $sformatf("Releasing %0s reset", reset_cause.name()), UVM_LOW)
    set_rstreqs(0);
    reset_done();
  endtask

  // Sends either a low power exit or an external hardware reset request, and drops it once it
  // should have caused the hardware to handle it.
  task send_reset(pwrmgr_pkg::reset_cause_e reset_cause,
                  logic [pwrmgr_pkg::TotalResetWidth-1:0] rstreqs, logic clear_it = 1);
    `uvm_info(`gfn, $sformatf("Sending %0s reset", reset_cause.name()), UVM_LOW)
    set_rstreqs(rstreqs);
    reset_start(reset_cause);
    if (clear_it) release_reset(reset_cause);
  endtask

  task send_scan_reset();
    `uvm_info(`gfn, "Sending scan reset.", UVM_MEDIUM)
    update_scanmode(prim_mubi_pkg::MuBi4True);
    cfg.io_div4_clk_rst_vif.wait_clks(scanmode_to_scan_rst_cycles);
    update_scan_rst_n(1'b0);
    set_pwrmgr_rst_reqs(.rst_lc_req('1), .rst_sys_req('1));
    set_reset_cause(pwrmgr_pkg::HwReq);
    // The clocks are turned off, so wait in time units.
    #1us;
    update_scanmode(prim_mubi_pkg::MuBi4False);
    update_scan_rst_n(1'b1);
    reset_done();
    // This makes sure the clock has restarted before this returns.
    cfg.io_div4_clk_rst_vif.wait_clks(1);
    `uvm_info(`gfn, "Done sending scan reset.", UVM_MEDIUM)
  endtask

  // Sends an ndm reset, and drops it once it should have
  // caused the hardware to handle it.
  task send_ndm_reset();
    set_ndmreset_req(1'b1);
    `uvm_info(`gfn, "Sending ndm reset", UVM_LOW)
    cfg.io_div4_clk_rst_vif.wait_clks(ndm_reset_cycles);
    set_ndmreset_req(1'b0);
  endtask

  // Requests a sw reset. It is cleared by hardware once the reset is taken.
  task send_sw_reset();
    `uvm_info(`gfn, "Sending sw reset", UVM_LOW)
    csr_wr(.ptr(ral.reset_req), .value(prim_mubi_pkg::MuBi4True));
    reset_start(pwrmgr_pkg::HwReq);
    cfg.io_div4_clk_rst_vif.wait_clks(non_ndm_reset_cycles);
    reset_done();
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    if (do_rstmgr_init) rstmgr_init();
    super.dut_init();
  endtask

  virtual task dut_shutdown();
    // check for pending rstmgr operations and wait for them to complete
    // TODO
  endtask

  task por_reset();
    cfg.rstmgr_vif.por_n = '0;
    cfg.aon_clk_rst_vif.wait_clks(POR_CLK_CYCLES);
    cfg.rstmgr_vif.por_n = '1;
    @(posedge cfg.rstmgr_vif.resets_o.rst_por_io_div4_n[0]);
  endtask

  task start_clocks();
    fork
      cfg.aon_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0),
                                      .reset_width_clks(BOGUS_RESET_CLK_CYCLES));
      cfg.io_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0),
                                     .reset_width_clks(BOGUS_RESET_CLK_CYCLES));
      cfg.io_div2_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0),
                                          .reset_width_clks(BOGUS_RESET_CLK_CYCLES));
      cfg.io_div4_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0),
                                          .reset_width_clks(BOGUS_RESET_CLK_CYCLES));
      cfg.main_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0),
                                       .reset_width_clks(BOGUS_RESET_CLK_CYCLES));
      cfg.usb_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0),
                                      .reset_width_clks(BOGUS_RESET_CLK_CYCLES));
    join
  endtask

  // This waits till the outgoing reset for the CPU goes inactive. It also waits at least one
  // aon cycle to make sure we don't drop por_n_i before SVA has time to detect the por_aon
  // reset went inactive.
  local task wait_for_cpu_out_of_reset();
    `DV_SPINWAIT_EXIT(wait (cfg.rstmgr_vif.resets_o.rst_sys_n[1] == 1'b1);,
                      cfg.clk_rst_vif.wait_clks(CPU_RESET_CLK_CYCLES);,
                      "timeout waiting for cpu reset inactive")
    cfg.aon_clk_rst_vif.wait_clks(1);
  endtask

  virtual task apply_reset(string kind = "HARD");
    fork
      por_reset();
      start_clocks();
      super.apply_reset(kind);
    join
  endtask

  task post_apply_reset(string reset_kind = "HARD");
    super.post_apply_reset(reset_kind);
    wait_for_cpu_out_of_reset();
  endtask

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    fork
      por_reset();
      start_clocks();
      super.apply_resets_concurrently(reset_duration_ps);
    join
  endtask

  // setup basic rstmgr features
  virtual task rstmgr_init();
    cfg.aon_clk_rst_vif.set_freq_mhz(AON_FREQ_MHZ);
    cfg.io_clk_rst_vif.set_freq_mhz(IO_FREQ_MHZ);
    cfg.io_div2_clk_rst_vif.set_freq_mhz(IO_DIV2_FREQ_MHZ);
    cfg.io_div4_clk_rst_vif.set_freq_mhz(IO_DIV4_FREQ_MHZ);
    cfg.main_clk_rst_vif.set_freq_mhz(MAIN_FREQ_MHZ);
    cfg.usb_clk_rst_vif.set_freq_mhz(USB_FREQ_MHZ);
    // Initial values for some input pins.
    cfg.rstmgr_vif.scanmode_i  = prim_mubi_pkg::MuBi4False;
    cfg.rstmgr_vif.scan_rst_ni = scan_rst_ni;
    set_pwrmgr_rst_reqs(1'b0, 1'b0);
    set_rstreqs('0);
    set_reset_cause(pwrmgr_pkg::ResetNone);
    set_ndmreset_req('0);
    set_rst_cpu_n('1);
  endtask

endclass : rstmgr_base_vseq
