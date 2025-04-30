// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
<%
from ipgen.clkmgr_gen import get_all_srcs, get_rg_srcs
from topgen.lib import Name
all_srcs = get_all_srcs(src_clks, derived_clks)
non_aon_src_names = sorted(
    s['name'] for s in src_clks.values() if not s['aon'])
all_src_names = sorted(s['name'] for s in all_srcs.values())
meas_clks = sorted(
    ((s['name'], s['freq']) for s in all_srcs.values()), key=lambda x: x[0])
rg_srcs = get_rg_srcs(typed_clocks)
%>\
class clkmgr_base_vseq extends cip_base_vseq #(
  .RAL_T              (clkmgr_reg_block),
  .CFG_T              (clkmgr_env_cfg),
  .COV_T              (clkmgr_env_cov),
  .VIRTUAL_SEQUENCER_T(clkmgr_virtual_sequencer)
);

  `uvm_object_utils(clkmgr_base_vseq)
  `uvm_object_new

  // The extra cycles to wait after reset before starting any test, required so some CSRs (notably
  // hints_status) are properly set when inputs go through synchronizers.
  localparam int POST_APPLY_RESET_CYCLES = 10;

  // This delay is needed to allow updates to the idle inputs to go through synchronizers and
  // counters.
  localparam int IDLE_SYNC_CYCLES = 20;

  // This is the timeout for the various clk status outputs to react to their inputs.
  localparam int CLK_STATUS_TIMEOUT_NS = 100_000;

% for clk_name in non_aon_src_names:
  rand bit              ${clk_name}_ip_clk_en;
% endfor

  rand mubi_hintables_t idle;

  // Override this from cip_base_vseq, since clkmgr tests are relatively short.
  constraint rand_reset_delay_c {
    rand_reset_delay dist {
      [1 : 1000]            :/ 1,
      [1001 : 100_000]      :/ 2,
      [100_001 : 1_000_000] :/ 6
    };
  }

  mubi4_t       scanmode;
  int           scanmode_on_weight          = 8;

  mubi4_t       extclk_ctrl_high_speed_sel;
  mubi4_t       extclk_ctrl_sel;
  clkmgr_mubi_e mubi_mode;

  // This holds the necessary per measure control CSR info.
  typedef struct {
    string name;
    dv_base_reg en;
    dv_base_reg_field ctrl_hi;
    dv_base_reg_field ctrl_lo;
  } meas_ctrl_regs_t;
  meas_ctrl_regs_t meas_ctrl_regs[clk_mesr_e];

  virtual function void set_scanmode_on_low_weight();
    scanmode_on_weight = 2;
  endfunction

  function void post_randomize();
    extclk_ctrl_high_speed_sel = get_rand_mubi4_val(6, 2, 2);
    extclk_ctrl_sel = get_rand_mubi4_val(4, 2, 2);
    scanmode = get_rand_mubi4_val(scanmode_on_weight, 4, 4);
    `uvm_info(`gfn, $sformatf(
              "randomize: extclk_ctrl_sel=0x%x, extclk_ctrl_high_speed_sel=0x%x, scanmode=0x%x",
              extclk_ctrl_sel,
              extclk_ctrl_high_speed_sel,
              scanmode
              ), UVM_MEDIUM)
    super.post_randomize();
  endfunction

  virtual task initialize_on_start();
    `uvm_info(`gfn, "In clkmgr_if initialize_on_start", UVM_MEDIUM)
    idle = {NUM_TRANS{MuBi4True}};
    scanmode = MuBi4False;
    cfg.clkmgr_vif.init(.idle(idle), .scanmode(scanmode), .lc_debug_en(Off));
% for clk_name in non_aon_src_names:
    ${clk_name}_ip_clk_en = 1'b1;
% endfor
    start_ip_clocks();
  endtask

  // Converts to bool with strict true.
  protected function hintables_t mubi_hintables_to_hintables(mubi_hintables_t mubi_hints);
    hintables_t ret;
    foreach (mubi_hints[i]) ret[i] = prim_mubi_pkg::mubi4_test_true_strict(mubi_hints[i]);
    return ret;
  endfunction

  local function void disable_unnecessary_exclusions();
    ral.get_excl_item().enable_excl("clkmgr_reg_block.clk_enables", 0);
    ral.get_excl_item().enable_excl("clkmgr_reg_block.clk_hints", 0);
    `uvm_info(`gfn, "Adjusted exclusions", UVM_MEDIUM)
    ral.get_excl_item().print_exclusions(UVM_MEDIUM);
  endfunction

  task pre_start();
% for src in rg_srcs:
<% spc = " " * (len("    ") +
                len("meas_ctrl_regs[ClkMesr") +
                len(Name.to_camel_case(src)) +
                len("}] = '{"))
%>\
    meas_ctrl_regs[ClkMesr${Name.to_camel_case(src)}] = '{"${src}", ral.${src}_meas_ctrl_en,
${spc}ral.${src}_meas_ctrl_shadowed.hi,
${spc}ral.${src}_meas_ctrl_shadowed.lo};
% endfor
    mubi_mode = ClkmgrMubiNone;
    `DV_GET_ENUM_PLUSARG(clkmgr_mubi_e, mubi_mode, clkmgr_mubi_mode)
    `uvm_info(`gfn, $sformatf("mubi_mode = %s", mubi_mode.name), UVM_MEDIUM)
    cfg.clkmgr_vif.init(.idle({NUM_TRANS{MuBi4True}}), .scanmode(scanmode), .lc_debug_en(Off));
% for src in sorted(src_clks.values(), key=lambda v: v['name']):
  % if not src['aon']:
    cfg.clkmgr_vif.update_${src['name']}_ip_clk_en(1'b1);
  % endif
% endfor
    cfg.clkmgr_vif.update_div_step_down_req(MuBi4False);
    cfg.clkmgr_vif.update_io_clk_byp_ack(MuBi4False);

    disable_unnecessary_exclusions();
    clkmgr_init();
    super.pre_start();
    if (common_seq_type inside {"shadow_reg_errors", "shadow_reg_errors_with_csr_rw"}) begin
      expect_fatal_alerts = 1;
    end
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
  endtask

  virtual task dut_shutdown();
    // check for pending clkmgr operations and wait for them to complete
  endtask

  // This turns on the actual input clocks, as the pwrmgr would.
  task start_ip_clocks();
    fork
% for clk_name in non_aon_src_names:
      start_${clk_name}_ip_clock();
% endfor
    join
  endtask

% for clk_name in non_aon_src_names:
  task start_${clk_name}_ip_clock();
    `uvm_info(`gfn, $sformatf(
              "starting ${clk_name} clk_en with current status %b", cfg.clkmgr_vif.pwr_o.${clk_name}_status),
              UVM_MEDIUM)
    cfg.${clk_name}_clk_rst_vif.start_clk();
    cfg.clkmgr_vif.pwr_i.${clk_name}_ip_clk_en = ${clk_name}_ip_clk_en;
    `DV_SPINWAIT(wait(cfg.clkmgr_vif.pwr_o.${clk_name}_status == 1'b1);,
                 "timeout waiting for ${clk_name}_status to raise", CLK_STATUS_TIMEOUT_NS)
    `uvm_info(`gfn, "starting ${clk_name} clock done", UVM_MEDIUM)
  endtask

% endfor
  // This turns on or off the actual input clocks, as the pwrmgr would.
  task control_ip_clocks();
    fork
% for clk_name in non_aon_src_names:
      control_${clk_name}_ip_clock();
% endfor
    join
  endtask

% for clk_name in non_aon_src_names:
  task control_${clk_name}_ip_clock();
    // Do nothing if nothing interesting changed.
    if (cfg.clkmgr_vif.pwr_i.${clk_name}_ip_clk_en == ${clk_name}_ip_clk_en) return;
    `uvm_info(`gfn, $sformatf(
              "controlling ${clk_name} clk_en from %b to %b with current status %b",
              cfg.clkmgr_vif.pwr_i.${clk_name}_ip_clk_en,
              ${clk_name}_ip_clk_en,
              cfg.clkmgr_vif.pwr_o.${clk_name}_status
              ), UVM_MEDIUM)
    if (!${clk_name}_ip_clk_en) begin
      cfg.clkmgr_vif.pwr_i.${clk_name}_ip_clk_en = ${clk_name}_ip_clk_en;
      `DV_SPINWAIT(wait(cfg.clkmgr_vif.pwr_o.${clk_name}_status == 1'b0);,
                   "timeout waiting for ${clk_name}_status to fall", CLK_STATUS_TIMEOUT_NS)
      cfg.${clk_name}_clk_rst_vif.stop_clk();
    end else begin
      cfg.${clk_name}_clk_rst_vif.start_clk();
      cfg.clkmgr_vif.pwr_i.${clk_name}_ip_clk_en = ${clk_name}_ip_clk_en;
      `DV_SPINWAIT(wait(cfg.clkmgr_vif.pwr_o.${clk_name}_status == 1'b1);,
                   "timeout waiting for ${clk_name}_status to raise", CLK_STATUS_TIMEOUT_NS)
    end
    `uvm_info(`gfn, "controlling ${clk_name} clock done", UVM_MEDIUM)
  endtask

% endfor
  task disable_frequency_measurement(clk_mesr_e which);
    `uvm_info(`gfn, $sformatf("Disabling frequency measurement for %0s", which.name), UVM_MEDIUM)
    csr_wr(.ptr(meas_ctrl_regs[which].en), .value(MuBi4False));
  endtask

  protected function int get_meas_ctrl_value(int min_threshold, int max_threshold,
                                             uvm_reg_field lo, uvm_reg_field hi);
    int lo_mask = (1 << lo.get_n_bits()) - 1;
    int hi_mask = (1 << hi.get_n_bits()) - 1;

    int value = (((min_threshold & lo_mask) << lo.get_lsb_pos()) |
                 ((max_threshold & hi_mask) << hi.get_lsb_pos()));
    return value;
  endfunction

  // Any non-false mubi value in the enable CSR turns measurements on.
  task enable_frequency_measurement(clk_mesr_e which, int min_threshold, int max_threshold);
    int value = get_meas_ctrl_value(min_threshold, max_threshold, meas_ctrl_regs[which].ctrl_lo,
                                    meas_ctrl_regs[which].ctrl_hi);
    mubi4_t en_value = get_rand_mubi4_val(1, 0, 3);
    `uvm_info(`gfn, $sformatf(
              "Enabling frequency measurement for %0s, min=0x%x, max=0x%x, expected=0x%x",
              which.name,
              min_threshold,
              max_threshold,
              ExpectedCounts[which]
              ), UVM_MEDIUM)
    csr_wr(.ptr(meas_ctrl_regs[which].ctrl_lo.get_dv_base_reg_parent()), .value(value));
    csr_wr(.ptr(meas_ctrl_regs[which].en), .value(en_value));
  endtask

  // This checks that when calibration is lost regwen should be re-enabled and measurements
  // disabled.
  task calibration_lost_checks();
    void'(ral.measure_ctrl_regwen.predict(1));
    csr_rd_check(.ptr(ral.measure_ctrl_regwen), .compare_value(1));
    foreach (ExpectedCounts[clk]) begin
      clk_mesr_e clk_mesr = clk_mesr_e'(clk);
      csr_rd_check(.ptr(meas_ctrl_regs[clk_mesr].en), .compare_value(MuBi4False));
    end
  endtask

  function control_meas_saturation_assert(clk_mesr_e clk, bit enable);
    `uvm_info(`gfn, $sformatf(
              "%sabling MaxWidth_A assertion for %s", enable ? "En" : "Dis", clk.name),
              UVM_MEDIUM)
    case (clk)
% for src in rg_srcs:
      ClkMesr${Name.to_camel_case(src)}: begin
        if (enable) $asserton(0, "tb.dut.u_${src}_meas.u_meas.MaxWidth_A");
        else $assertoff(0, "tb.dut.u_${src}_meas.u_meas.MaxWidth_A");
      end
% endfor
      default: `uvm_error(`gfn, $sformatf("unexpected clock index '%0d'", clk))
    endcase
  endfunction

  local function void control_sync_pulse_assert(clk_mesr_e clk, bit enable);
    case (clk)
% for src in rg_srcs:
      ClkMesr${Name.to_camel_case(src)}: begin
        if (enable) $asserton(0, "tb.dut.u_${src}_meas.u_meas.u_sync_ref.SrcPulseCheck_M");
        else $assertoff(0, "tb.dut.u_${src}_meas.u_meas.u_sync_ref.SrcPulseCheck_M");
      end
% endfor
      default: `uvm_error(`gfn, $sformatf("unexpected clock index '%0d'", clk))
    endcase
  endfunction

  // This turns off/on some clocks being measured to trigger a measurement timeout.
  // A side-effect is that some RTL assertions will fire, so they are corresponsdingly controlled.
  task disturb_measured_clock(clk_mesr_e clk, bit enable);
    case (clk)
% for src in rg_srcs:
<%
  if src in derived_clks:
    root_name = derived_clks[src]['src']['name']
  else:
    root_name = src
%>\
      ClkMesr${Name.to_camel_case(src)}: begin
        `uvm_info(`gfn, $sformatf("%sabling %s clk", enable ? "En" : "Dis", "${root_name}"),
                  UVM_MEDIUM)
        if (enable) cfg.${root_name}_clk_rst_vif.start_clk();
        else cfg.${root_name}_clk_rst_vif.stop_clk();
        control_sync_pulse_assert(.clk(ClkMesr${Name.to_camel_case(src)}), .enable(enable));
      end
% endfor
      default: `uvm_fatal(`gfn, $sformatf("Unexpected clk '%0d'", clk))
    endcase
  endtask

  function void report_recov_error_mismatch(string error_type, recov_bits_t expected,
                                            recov_bits_t actual);
    recov_bits_t mismatch = actual ^ expected;
    foreach (mismatch[clk]) begin
      clk_mesr_e clk_mesr = clk_mesr_e'(clk);
      if (mismatch[clk]) begin
        `uvm_info(`gfn, $sformatf(
                  "Mismatch %0s for %0s, expected %b, actual %b",
                  error_type,
                  clk_mesr.name,
                  expected[clk],
                  actual[clk]
                  ), UVM_LOW)
      end
    end
    `uvm_error(`gfn, $sformatf(
               "Mismatch for %0s recoverable error, expected 0b%b, got 0b%b",
               error_type,
               expected,
               actual
               ))
  endfunction

  // This is tricky, and we choose to handle it all here, not in "super":
  // - there are no multiple clk_rst_vifs,
  // - it would be too complicated to coordinate reset durations with super.
  // For hard resets we also reset the cfg.root*_clk_rst_vif, and its reset is shorter than
  // that of all others.
  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    int clk_periods_q[$] = {
      reset_duration_ps,
% for src_name in all_src_names:
<% sep = "" if loop.last else "," %>\
      cfg.${src_name}_clk_rst_vif.clk_period_ps${sep}
% endfor
    };
    reset_duration_ps = max(clk_periods_q);

    `uvm_info(`gfn, "In apply_resets_concurrently", UVM_MEDIUM)
    cfg.clk_rst_vif.drive_rst_pin(0);
% for clk_family in parent_child_clks.values():
  % for src in clk_family:
    cfg.root_${src}_clk_rst_vif.drive_rst_pin(0);
  % endfor
% endfor
% for src_name in all_src_names:
    cfg.${src_name}_clk_rst_vif.drive_rst_pin(0);
% endfor

    #(reset_duration_ps * $urandom_range(2, 10) * 1ps);
% for clk_family in parent_child_clks.values():
  % for src in clk_family:
    cfg.root_${src}_clk_rst_vif.drive_rst_pin(1);
  % endfor
% endfor
    `uvm_info(`gfn, "apply_resets_concurrently releases POR", UVM_MEDIUM)

    #(reset_duration_ps * $urandom_range(2, 10) * 1ps);
    cfg.clk_rst_vif.drive_rst_pin(1);
% for src_name in all_src_names:
    cfg.${src_name}_clk_rst_vif.drive_rst_pin(1);
% endfor
    `uvm_info(`gfn, "apply_resets_concurrently releases other resets", UVM_MEDIUM)
  endtask

  virtual task apply_reset(string kind = "HARD");
    if (kind == "HARD") apply_resets_concurrently();
    else begin
      fork
        cfg.clk_rst_vif.apply_reset();
% for src_name in all_src_names:
        cfg.${src_name}_clk_rst_vif.apply_reset();
% endfor
      join
    end
  endtask

  task post_apply_reset(string reset_kind = "HARD");
    super.post_apply_reset(reset_kind);
    initialize_on_start();
    cfg.io_clk_rst_vif.wait_clks(POST_APPLY_RESET_CYCLES);
  endtask

  // setup basic clkmgr features
  virtual task clkmgr_init();
    // Initialize input clock frequencies.
% for src in src_clks.values():
  % if not src['aon']:
    cfg.${src['name']}_clk_rst_vif.set_freq_mhz((1.0 * ${f"{src['freq']:_}"}) / 1_000_000);
  % endif
% endfor
    // The real clock rate for aon is 200kHz, but that can slow testing down.
    // Increasing its frequency improves DV efficiency without compromising quality.
    cfg.aon_clk_rst_vif.set_freq_mhz((1.0 * FakeAonClkHz) / 1_000_000);
  endtask
endclass : clkmgr_base_vseq
