// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rstmgr_base_vseq extends cip_base_vseq #(
  .RAL_T              (rstmgr_reg_block),
  .CFG_T              (rstmgr_env_cfg),
  .COV_T              (rstmgr_env_cov),
  .VIRTUAL_SEQUENCER_T(rstmgr_virtual_sequencer)
);

  `uvm_object_utils(rstmgr_base_vseq)

  `uvm_object_new

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

  // The different types of reset.
  typedef enum int {
    ResetPOR,
    ResetScan,
    ResetLowPower,
    ResetSw,
    ResetHw,
    ResetLast
  } reset_e;

  // The reset_info adds POR and low power to TotalResetWidth.
  typedef logic [pwrmgr_pkg::TotalResetWidth+2-1:0] reset_info_t;
  typedef logic [pwrmgr_pkg::HwResetWidth-1:0] rstreqs_t;

  rand sw_rst_t          sw_rst_regwen;
  rand sw_rst_t          sw_rst_ctrl_n;

  bit                    reset_once;

  rand cpu_crash_dump_t  cpu_dump;
  rand alert_crashdump_t alert_dump;

  rand rstreqs_t         rstreqs;

  rand logic             scan_rst_ni;
  constraint scan_rst_ni_c {scan_rst_ni == 1;}

  // Various cycles for delaying stimulus.
  rand int rst_to_req_cycles;
  constraint rst_to_req_cycles_c {rst_to_req_cycles inside {[1 : 6]};}

  rand int release_lc_to_release_sys_cycles;
  constraint release_lc_to_release_sys_cycles_c {
    release_lc_to_release_sys_cycles inside {[1 : 10]};
  }

  rand int scan_rst_cycles;
  constraint scan_rst_cycles_c {scan_rst_cycles inside {[0 : 4]};}

  rand int scanmode_cycles;
  constraint scanmode_cycles_c {scanmode_cycles inside {[0 : 4]};}

  rand int lowpower_rst_cycles;
  constraint lowpower_rst_cycles_c {lowpower_rst_cycles inside {[0 : 20]};}

  rand int sw_rst_cycles;
  constraint sw_rst_cycles_c {sw_rst_cycles inside {[0 : 20]};}

  rand int hw_rst_cycles;
  constraint hw_rst_cycles_c {hw_rst_cycles inside {[0 : 20]};}

  rand int reset_us;
  constraint reset_us_c {reset_us inside {[1 : 4]};}

  bit do_rstmgr_init = 1'b1;

  mubi4_t scanmode;
  int scanmode_on_weight = 8;

  // This is used to randomize the delays for the clocks to start and stop.
  typedef struct {
    bit [5:0] io_delay;
    bit [5:0] io_div2_delay;
    bit [5:0] io_div4_delay;
    bit [5:0] main_delay;
    bit [5:0] usb_delay;
  } clock_delays_in_ns_t;

  // What to expect when testing resets.
  string reset_name[reset_e] = '{
    ResetPOR: "POR",
    ResetScan: "scan",
    ResetLowPower: "low power",
    ResetSw: "software",
    ResetHw: "hardware"
  };

  function int get_reset_code(reset_e reset, rstreqs_t rstreqs);
    case (reset)
      ResetPOR, ResetScan: return 1 << ral.reset_info.por.get_lsb_pos();
      ResetLowPower: return 1 << ral.reset_info.low_power_exit.get_lsb_pos();
      ResetSw: return 1 << ral.reset_info.sw_reset.get_lsb_pos();
      ResetHw: return rstreqs << ral.reset_info.hw_req.get_lsb_pos();
      default: `uvm_error(`gfn, $sformatf("Unexpected reset code %0d", reset))
    endcase
  endfunction

  function void post_randomize();
    scanmode = get_rand_mubi4_val(scanmode_on_weight, 4, 4);
  endfunction

  local function void update_scanmode(prim_mubi_pkg::mubi4_t value);
    cfg.rstmgr_vif.scanmode_i = value;
  endfunction

  local function void update_scan_rst_n(logic value);
    cfg.rstmgr_vif.scan_rst_ni = value;
  endfunction

  local function void set_pwrmgr_rst_reqs(logic rst_lc_req, logic rst_sys_req);
    `uvm_info(`gfn, $sformatf("Setting pwr_i lc_req=%x sys_req=%x", rst_lc_req, rst_sys_req),
              UVM_MEDIUM)
    cfg.rstmgr_vif.pwr_i.rst_lc_req  = {rstmgr_pkg::PowerDomains{rst_lc_req}};
    cfg.rstmgr_vif.pwr_i.rst_sys_req = {rstmgr_pkg::PowerDomains{rst_sys_req}};
  endfunction

  local function void set_rstreqs(rstreqs_t rstreqs);
    cfg.rstmgr_vif.pwr_i.rstreqs = rstreqs;
  endfunction

  local function void add_rstreqs(rstreqs_t rstreqs);
    cfg.rstmgr_vif.pwr_i.rstreqs |= rstreqs;
    `uvm_info(`gfn, $sformatf("Updating rstreqs to 0x%x", cfg.rstmgr_vif.pwr_i.rstreqs), UVM_MEDIUM)
  endfunction

  local function void set_reset_cause(pwrmgr_pkg::reset_cause_e reset_cause);
    cfg.rstmgr_vif.pwr_i.reset_cause = reset_cause;
  endfunction

  static function logic is_running_sequence(string seq_name);
    string actual_sequence = "none";
    // Okay to ignore return value since the default won't match.
    void'($value$plusargs("UVM_TEST_SEQ=%0s", actual_sequence));
    return actual_sequence.compare(seq_name) == 0;
  endfunction

  virtual protected task check_reset_info(logic [TL_DW-1:0] expected_value,
                                          string msg = "reset_info mismatch");
    csr_rd_check(.ptr(ral.reset_info), .compare_value(expected_value), .err_msg(msg));
  endtask

  local function void set_cpu_dump_info(cpu_crash_dump_t cpu_dump);
    `uvm_info(`gfn, $sformatf("Setting cpu_dump_i to %p", cpu_dump), UVM_MEDIUM)
    cfg.rstmgr_vif.cpu_dump_i = cpu_dump;
  endfunction

  local task check_cpu_dump_info(cpu_crash_dump_t cpu_dump);
    `uvm_info(`gfn, "Checking cpu_info", UVM_MEDIUM)
    csr_wr(.ptr(ral.cpu_info_ctrl.index), .value(7));
    csr_rd_check(.ptr(ral.cpu_info), .compare_value(cpu_dump.prev_valid),
                 .err_msg("checking previous_valid"));
    csr_wr(.ptr(ral.cpu_info_ctrl.index), .value(6));
    csr_rd_check(.ptr(ral.cpu_info), .compare_value(cpu_dump.prev_exception_pc),
                 .err_msg("checking previous exception_pc"));
    csr_wr(.ptr(ral.cpu_info_ctrl.index), .value(5));
    csr_rd_check(.ptr(ral.cpu_info), .compare_value(cpu_dump.prev_exception_addr),
                 .err_msg("checking previous exception_addr"));
    csr_wr(.ptr(ral.cpu_info_ctrl.index), .value(4));
    csr_rd_check(.ptr(ral.cpu_info), .compare_value(cpu_dump.current.current_pc),
                 .err_msg("checking current current_pc"));
    csr_wr(.ptr(ral.cpu_info_ctrl.index), .value(3));
    csr_rd_check(.ptr(ral.cpu_info), .compare_value(cpu_dump.current.next_pc),
                 .err_msg("checking current next_pc"));
    csr_wr(.ptr(ral.cpu_info_ctrl.index), .value(2));
    csr_rd_check(.ptr(ral.cpu_info), .compare_value(cpu_dump.current.last_data_addr),
                 .err_msg("checking current last_data_addr"));
    csr_wr(.ptr(ral.cpu_info_ctrl.index), .value(1));
    csr_rd_check(.ptr(ral.cpu_info), .compare_value(cpu_dump.current.exception_pc),
                 .err_msg("checking current exception_pc"));
    csr_wr(.ptr(ral.cpu_info_ctrl.index), .value(0));
    csr_rd_check(.ptr(ral.cpu_info), .compare_value(cpu_dump.current.exception_addr),
                 .err_msg("checking current exception_addr"));

  endtask

  local function void set_alert_dump_info(alert_crashdump_t alert_dump);
    `uvm_info(`gfn, $sformatf(
              "Setting alert_dump_i to 0x%x", linearized_alert_dump_t'({>>{alert_dump}})),
              UVM_MEDIUM)
    cfg.rstmgr_vif.alert_dump_i = alert_dump;
  endfunction

  local task check_alert_dump_info(alert_crashdump_t alert_dump);
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

  virtual protected task set_alert_info_for_capture(alert_crashdump_t alert_dump, logic enable);
    set_alert_dump_info(alert_dump);
    `uvm_info(`gfn, $sformatf("%0sabling alert_info capture", (enable ? "En" : "Dis")), UVM_MEDIUM)
    csr_wr(.ptr(ral.alert_info_ctrl.en), .value(enable));
  endtask

  virtual protected task set_cpu_info_for_capture(cpu_crash_dump_t cpu_dump, logic enable);
    set_cpu_dump_info(cpu_dump);
    `uvm_info(`gfn, $sformatf("%0sabling cpu_info capture", (enable ? "En" : "Dis")), UVM_MEDIUM)
    csr_wr(.ptr(ral.cpu_info_ctrl.en), .value(enable));
  endtask

  virtual protected task set_alert_and_cpu_info_for_capture(alert_crashdump_t alert_dump,
                                                            cpu_crash_dump_t cpu_dump);
    set_alert_info_for_capture(alert_dump, 1'b1);
    set_cpu_info_for_capture(cpu_dump, 1'b1);
  endtask

  virtual protected task check_alert_info_after_reset(alert_crashdump_t alert_dump, logic enable);
    csr_rd_check(.ptr(ral.alert_info_ctrl.en), .compare_value(enable),
                 .err_msg($sformatf("Expected alert info capture enable %b", enable)));
    csr_wr(.ptr(ral.alert_info_ctrl.en), .value(enable));
    check_alert_dump_info(alert_dump);
  endtask

  virtual protected task check_cpu_info_after_reset(cpu_crash_dump_t cpu_dump, logic enable);
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
  virtual protected task check_alert_and_cpu_info_after_reset(
      alert_crashdump_t alert_dump, cpu_crash_dump_t cpu_dump, logic enable);
    check_alert_info_after_reset(alert_dump, enable);
    check_cpu_info_after_reset(cpu_dump, enable);
  endtask

  virtual protected task clear_alert_and_cpu_info();
    set_alert_and_cpu_info_for_capture('0, '0);
    send_sw_reset();
    cfg.io_div4_clk_rst_vif.wait_clks(20);  // # of lc reset cycles measured from waveform
    check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(0));
  endtask

  virtual protected task clear_sw_rst_ctrl_n();
    const sw_rst_t sw_rst_all_ones = '1;
    rstmgr_csr_wr_unpack(.ptr(ral.sw_rst_ctrl_n), .value(sw_rst_all_ones));
    rstmgr_csr_rd_check_unpack(.ptr(ral.sw_rst_ctrl_n), .compare_value(sw_rst_all_ones),
                               .err_msg("Expected sw_rst_ctrl_n to be set"));
  endtask

  virtual protected task clear_sw_rst_ctrl_n_per_entry(int entry);
    csr_wr(.ptr(ral.sw_rst_ctrl_n[entry]), .value(1'b1));
    csr_rd_check(.ptr(ral.sw_rst_ctrl_n[entry]), .compare_value(1'b1),
                 .err_msg($sformatf("Expected sw_rst_ctrl_n[%0d] to be set", entry)));
  endtask

  virtual protected task check_sw_rst_regwen(sw_rst_t expected_regwen);
    rstmgr_csr_rd_check_unpack(.ptr(ral.sw_rst_regwen), .compare_value(expected_regwen),
                               .err_msg("Mismatching sw_rst_regwen"));
  endtask

  // Stimulate and check sw_rst_ctrl_n with a given sw_rst_regwen setting.
  // Exit when a reset is detected or the sequence would be invalid and may get stuck.
  virtual protected task check_sw_rst_ctrl_n(sw_rst_t sw_rst_ctrl_n, sw_rst_t sw_rst_regwen,
                                             bit erase_ctrl_n);
    sw_rst_t exp_ctrl_n = ~sw_rst_regwen | sw_rst_ctrl_n;

    `uvm_info(`gfn, $sformatf(
              "Setting sw_rst_ctrl_n to 0x%0x with regwen 0x%x, expect 0x%x",
              sw_rst_ctrl_n,
              sw_rst_regwen,
              exp_ctrl_n
              ), UVM_MEDIUM)
    foreach (ral.sw_rst_ctrl_n[i]) begin
      if (under_reset) return;
      csr_wr(.ptr(ral.sw_rst_ctrl_n[i]), .value(sw_rst_ctrl_n[i]));
      if (under_reset) return;
      csr_rd_check(.ptr(ral.sw_rst_ctrl_n[i]), .compare_value(exp_ctrl_n[i]),
                   .err_msg($sformatf("Mismatch for bit %0d", i)));
    end
    if (erase_ctrl_n && !under_reset) clear_sw_rst_ctrl_n();
  endtask

  virtual protected task check_sw_rst_ctrl_n_per_entry(
      sw_rst_t sw_rst_ctrl_n, sw_rst_t sw_rst_regwen, bit erase_ctrl_n, int entry);
    sw_rst_t exp_ctrl_n;

    `uvm_info(`gfn, $sformatf("Set sw_rst_ctrl_n[%0d] to 0x%0x", entry, sw_rst_ctrl_n), UVM_MEDIUM)
    csr_wr(.ptr(ral.sw_rst_ctrl_n[entry]), .value(sw_rst_ctrl_n[entry]));
    // And check that the reset outputs match the actual ctrl_n settings.
    // Allow for domain crossing delay.
    cfg.io_div2_clk_rst_vif.wait_clks(3);
    exp_ctrl_n = ~sw_rst_regwen | sw_rst_ctrl_n;
    `uvm_info(`gfn, $sformatf(
              "regwen=%b, ctrl_n=%b, expected=%b", sw_rst_regwen, sw_rst_ctrl_n, exp_ctrl_n),
              UVM_MEDIUM)
    csr_rd_check(.ptr(ral.sw_rst_ctrl_n[entry]), .compare_value(exp_ctrl_n[entry]),
                 .err_msg($sformatf("Expected enabled updates in sw_rst_ctrl_n[%0d]", entry)));
    if (erase_ctrl_n) clear_sw_rst_ctrl_n_per_entry(entry);
  endtask

  local task control_all_clocks(bit enable);
    // Randomize the delays for each clock turning on or off.
    clock_delays_in_ns_t delays;
    `DV_CHECK_STD_RANDOMIZE_FATAL(delays)
    if (enable) fork
      #(delays.io_delay * 1ns) cfg.io_clk_rst_vif.start_clk();
      #(delays.io_div2_delay * 1ns) cfg.io_div2_clk_rst_vif.start_clk();
      #(delays.io_div4_delay * 1ns) cfg.io_div4_clk_rst_vif.start_clk();
      #(delays.main_delay * 1ns) cfg.main_clk_rst_vif.start_clk();
      #(delays.usb_delay * 1ns) cfg.usb_clk_rst_vif.start_clk();
    join else fork
      #(delays.io_delay * 1ns) cfg.io_clk_rst_vif.stop_clk();
      #(delays.io_div2_delay * 1ns) cfg.io_div2_clk_rst_vif.stop_clk();
      #(delays.io_div4_delay * 1ns) cfg.io_div4_clk_rst_vif.stop_clk();
      #(delays.main_delay * 1ns) cfg.main_clk_rst_vif.stop_clk();
      #(delays.usb_delay * 1ns) cfg.usb_clk_rst_vif.stop_clk();
    join
  endtask

  // Happens with hardware resets.
  local task reset_start(pwrmgr_pkg::reset_cause_e reset_cause);
    `uvm_info(`gfn, $sformatf("Starting pwrmgr inputs for %0s request", reset_cause.name()),
              UVM_MEDIUM)
    set_reset_cause(reset_cause);
    // These lag the reset requests since they are set after the pwrmgr fast fsm has made some
    // state transitions.
    cfg.io_div4_clk_rst_vif.wait_clks(rst_to_req_cycles);
    set_pwrmgr_rst_reqs(.rst_lc_req('1), .rst_sys_req('1));
    cfg.clk_rst_vif.stop_clk();
    if (reset_cause == pwrmgr_pkg::LowPwrEntry) begin
      control_all_clocks(.enable(0));
    end
  endtask

  protected task wait_till_active();
    // And wait for the main reset to be done.
    `DV_WAIT(cfg.rstmgr_vif.rst_ni_inactive, "Time-out waiting for rst_ni becoming inactive");
    // And wait a few cycles for settling before allowing the sequences to start.
    cfg.io_div4_clk_rst_vif.wait_clks(8);
  endtask

  protected task reset_done();
    `uvm_info(`gfn, "Releasing reset", UVM_LOW)
    update_scanmode(prim_mubi_pkg::MuBi4False);
    update_scan_rst_n(1'b1);
    if (cfg.rstmgr_vif.pwr_i.reset_cause == pwrmgr_pkg::LowPwrEntry) begin
      control_all_clocks(.enable(1));
    end
    cfg.clk_rst_vif.start_clk();
    cfg.io_div4_clk_rst_vif.wait_clks(10);
    set_reset_cause(pwrmgr_pkg::ResetNone);
    set_pwrmgr_rst_reqs(.rst_lc_req('0), .rst_sys_req('1));
    cfg.io_div4_clk_rst_vif.wait_clks(release_lc_to_release_sys_cycles);
    set_pwrmgr_rst_reqs(.rst_lc_req('0), .rst_sys_req('0));
    set_rstreqs(0);
    wait_till_active();
    `uvm_info(`gfn, "Reset done", UVM_MEDIUM)
  endtask

  // Sends either an external hardware reset request, setting the possibly different
  // rstreqs bits at different times. It optionally completes the reset.
  virtual protected task send_hw_reset(rstreqs_t rstreqs, logic complete_it = 1);
    `uvm_info(`gfn, $sformatf("Sending hw reset with 0b%0b", rstreqs), UVM_LOW)
    reset_start(pwrmgr_pkg::HwReq);
    fork
      begin : isolation_fork
        foreach (rstreqs[i]) begin : loop
          if (rstreqs[i]) begin
            fork
              automatic int index = i;
              automatic bit [2:0] cycles;
              `DV_CHECK_STD_RANDOMIZE_FATAL(cycles)
              cfg.io_div4_clk_rst_vif.wait_clks(cycles);
              add_rstreqs(rstreqs & (1 << index));
            join_none
          end
        end : loop
        wait fork;
      end : isolation_fork
    join
    if (complete_it) reset_done();
  endtask

  virtual protected task send_lowpower_reset(bit complete_it = 1);
    `uvm_info(`gfn, "Sending low power reset", UVM_LOW)
    reset_start(pwrmgr_pkg::LowPwrEntry);
    if (complete_it) reset_done();
  endtask


  // Lead with scan_rst active to avoid some derived sequence changing scanmode_i in such
  // a way it defeats this reset.
  virtual protected task send_scan_reset(bit complete_it = 1);
    `uvm_info(`gfn, "Sending scan reset", UVM_MEDIUM)
    fork
      begin
        cfg.io_div4_clk_rst_vif.wait_clks(scan_rst_cycles);
        update_scan_rst_n(1'b0);
      end
      begin
        cfg.io_div4_clk_rst_vif.wait_clks(scanmode_cycles);
        update_scanmode(prim_mubi_pkg::MuBi4True);
      end
    join
    reset_start(pwrmgr_pkg::HwReq);

    // The clocks are turned off, so wait in time units.
    #(reset_us * 1us);
    if (complete_it) reset_done();
  endtask

  // Requests a sw reset. It is cleared by hardware once the reset is taken.
  virtual protected task send_sw_reset(bit complete_it = 1);
    `uvm_info(`gfn, "Sending sw reset", UVM_LOW)
    reset_start(pwrmgr_pkg::HwReq);
    #(reset_us * 1us);
    if (complete_it) reset_done();
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    if (do_rstmgr_init) rstmgr_init();
    super.dut_init();
  endtask

  virtual task dut_shutdown();
    // No checks seem needed.
  endtask

  local task start_clocks();
    control_all_clocks(.enable(1));
    fork
      cfg.aon_clk_rst_vif.apply_reset(.reset_width_clks(BOGUS_RESET_CLK_CYCLES));
      cfg.io_clk_rst_vif.apply_reset(.reset_width_clks(BOGUS_RESET_CLK_CYCLES));
      cfg.io_div2_clk_rst_vif.apply_reset(.reset_width_clks(BOGUS_RESET_CLK_CYCLES));
      cfg.io_div4_clk_rst_vif.apply_reset(.reset_width_clks(BOGUS_RESET_CLK_CYCLES));
      cfg.main_clk_rst_vif.apply_reset(.reset_width_clks(BOGUS_RESET_CLK_CYCLES));
      cfg.usb_clk_rst_vif.apply_reset(.reset_width_clks(BOGUS_RESET_CLK_CYCLES));
    join
  endtask

  protected task por_reset_done(bit complete_it);
    cfg.rstmgr_vif.por_n = '1;
    reset_start(pwrmgr_pkg::ResetUndefined);
    #(reset_us * 1us);
    if (complete_it) reset_done();
  endtask

  virtual protected task por_reset(bit complete_it = 1);
    `uvm_info(`gfn, "Starting POR", UVM_MEDIUM)
    cfg.rstmgr_vif.por_n = '0;
    control_all_clocks(.enable(0));
    #(100 * 1ns);
    start_clocks();
    cfg.aon_clk_rst_vif.wait_clks(POR_CLK_CYCLES);
    por_reset_done(complete_it);
  endtask

  virtual task apply_reset(string kind = "HARD");
    fork
      por_reset();
      super.apply_reset(kind);
    join
  endtask

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    fork
      por_reset();
      start_clocks();
      super.apply_resets_concurrently(reset_duration_ps);
    join
    `uvm_info(`gfn, "Done with apply_resets_concurrently", UVM_MEDIUM)
  endtask

  // Disable exclusions for RESET_REQ since they cause trouble for full-chip only.
  function void disable_unnecessary_exclusions();
    csr_excl_item csr_excl = ral.get_excl_item();
    `uvm_info(`gfn, "Dealing with exclusions", UVM_MEDIUM)
    csr_excl.enable_excl(.obj("rstmgr_reg_block.reset_req"), .enable(1'b0));
    csr_excl.print_exclusions(UVM_MEDIUM);
  endfunction

  task pre_start();
    if (do_rstmgr_init) rstmgr_init();
    disable_unnecessary_exclusions();
    super.pre_start();
  endtask

  // setup basic rstmgr features
  virtual task rstmgr_init();
    // Must set clk_rst_vif frequency to IO_DIV4_FREQ_MHZ since they are gated
    // versions of each other and have no clock domain crossings.
    // Notice they may still end up out of phase due to the way they get started.
    cfg.clk_rst_vif.set_freq_mhz(IO_DIV4_FREQ_MHZ);
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
  endtask

  // csr method wrapper for unpacked array registers
  virtual task rstmgr_csr_rd_check_unpack(
      input uvm_object ptr[], input uvm_reg_data_t compare_value = 0, input string err_msg = "");
    foreach (ptr[i]) begin
      if (cfg.under_reset) return;
      csr_rd_check(.ptr(ptr[i]), .compare_value(compare_value[i]), .err_msg(err_msg));
    end
  endtask : rstmgr_csr_rd_check_unpack

  virtual task rstmgr_csr_wr_unpack(input uvm_object ptr[], input uvm_reg_data_t value);
    foreach (ptr[i]) begin
      if (cfg.under_reset) return;
      csr_wr(.ptr(ptr[i]), .value(value[i]));
    end
  endtask
endclass : rstmgr_base_vseq
