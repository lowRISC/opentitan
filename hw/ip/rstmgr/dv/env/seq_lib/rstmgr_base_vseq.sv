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

  localparam int RESET_CLK_PERIODS = 5;
  // This needs to be longer than RESET_CLK_PERIODS times the slowest clock,
  // which is the AON's.
  localparam int DELAY_FOR_RESETS_CONCURRENTLY_PS = 5_000_000;

  typedef enum {
    LcTxTSelOn,
    LcTxTSelOff,
    LcTxTSelOther
  } lc_tx_t_sel_e;

  // This simplifies the constraint blocks.
  function lc_ctrl_pkg::lc_tx_t get_lc_tx_t_from_sel(lc_tx_t_sel_e sel, lc_ctrl_pkg::lc_tx_t other);
    case (sel)
      LcTxTSelOn: return lc_ctrl_pkg::On;
      LcTxTSelOff: return lc_ctrl_pkg::Off;
      LcTxTSelOther: return other;
    endcase
  endfunction

  rand lc_ctrl_pkg::lc_tx_t scanmode_other;
  rand lc_tx_t_sel_e        sel_scanmode;
  int                       scanmode_on_weight = 8;

  constraint scanmode_c {
    sel_scanmode dist {
      LcTxTSelOn    := scanmode_on_weight,
      LcTxTSelOff   := 4,
      LcTxTSelOther := 4
    };
    !(scanmode_other inside {lc_ctrl_pkg::On, lc_ctrl_pkg::Off});
  }

  pwrmgr_pkg::pwr_rst_req_t pwr_i;

  rand logic scan_rst_ni;
  constraint scan_rst_ni_c {scan_rst_ni == 1;}

  lc_ctrl_pkg::lc_tx_t scanmode;

  // various knobs to enable certain routines
  bit do_rstmgr_init = 1'b1;

  `uvm_object_new

  function void set_pwrmgr_rst_reqs(logic rst_lc_req, logic rst_sys_req);
    cfg.rstmgr_vif.pwr_i.rst_lc_req  = rst_lc_req;
    cfg.rstmgr_vif.pwr_i.rst_sys_req = rst_sys_req;
  endfunction

  function void set_rstreqs(logic [pwrmgr_reg_pkg::NumRstReqs:0] rstreqs);
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

  function void post_randomize();
    // TODO Some of these should go in rstmgr_ or dut_init.
    cfg.rstmgr_vif.scanmode_i  = lc_ctrl_pkg::Off;
    cfg.rstmgr_vif.scan_rst_ni = scan_rst_ni;
    set_pwrmgr_rst_reqs(1'b0, 1'b0);
    set_rstreqs('0);
    set_reset_cause(pwrmgr_pkg::ResetNone);
    set_ndmreset_req('0);
    set_rst_cpu_n('1);
  endfunction

  virtual task dut_init(string reset_kind = "HARD");
    if (do_rstmgr_init) rstmgr_init();
    super.dut_init();
  endtask

  virtual task dut_shutdown();
    // check for pending rstmgr operations and wait for them to complete
    // TODO
  endtask

  task fork_resets();
    fork
      cfg.aon_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0), .reset_width_clks(RESET_CLK_PERIODS));
      cfg.io_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0), .reset_width_clks(RESET_CLK_PERIODS));
      cfg.io_div2_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0),
                                          .reset_width_clks(RESET_CLK_PERIODS));
      cfg.io_div4_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0),
                                          .reset_width_clks(RESET_CLK_PERIODS));
      cfg.main_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0),
                                       .reset_width_clks(RESET_CLK_PERIODS));
      cfg.usb_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0), .reset_width_clks(RESET_CLK_PERIODS));
    join
  endtask

  local function real freq_mhz_to_ps(real freq);
    return 1e12 / (freq * 1_000_000.0);
  endfunction

  // This adds enough delay to cover the stretched delay, which is around 32 AON cycles.
  local task wait_for_reset_stretcher();
    cfg.aon_clk_rst_vif.wait_clks(50);
  endtask

  virtual task apply_reset(string kind = "HARD");
    `DV_CHECK_LT(freq_mhz_to_ps(AON_FREQ_MHZ) * RESET_CLK_PERIODS, DELAY_FOR_RESETS_CONCURRENTLY_PS,
                 $sformatf(
                 "apply_resets_concurrently delay (%0d) must exceed slowest reset (%0d)",
                 DELAY_FOR_RESETS_CONCURRENTLY_PS,
                 freq_mhz_to_ps(
                     AON_FREQ_MHZ
                 ) * RESET_CLK_PERIODS
                 ))
    fork
      super.apply_reset(kind);
      if (kind == "HARD") begin
        // Apply reset to all clk_rst_if instances so the clocks start, even if
        // the rst_n output is not connected.
        fork_resets();
      end
    join
    wait_for_reset_stretcher();
  endtask

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.aon_clk_rst_vif.drive_rst_pin(0);
    cfg.io_clk_rst_vif.drive_rst_pin(0);
    cfg.io_div2_clk_rst_vif.drive_rst_pin(0);
    cfg.io_div4_clk_rst_vif.drive_rst_pin(0);
    cfg.main_clk_rst_vif.drive_rst_pin(0);
    cfg.usb_clk_rst_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(DELAY_FOR_RESETS_CONCURRENTLY_PS);
    cfg.aon_clk_rst_vif.drive_rst_pin(1);
    cfg.io_clk_rst_vif.drive_rst_pin(1);
    cfg.io_div2_clk_rst_vif.drive_rst_pin(1);
    cfg.io_div4_clk_rst_vif.drive_rst_pin(1);
    cfg.main_clk_rst_vif.drive_rst_pin(1);
    cfg.usb_clk_rst_vif.drive_rst_pin(1);
    wait_for_reset_stretcher();
  endtask

  // setup basic rstmgr features
  virtual task rstmgr_init();
    cfg.aon_clk_rst_vif.set_freq_mhz(AON_FREQ_MHZ);
    cfg.io_clk_rst_vif.set_freq_mhz(IO_FREQ_MHZ);
    cfg.io_div2_clk_rst_vif.set_freq_mhz(IO_DIV2_FREQ_MHZ);
    cfg.io_div4_clk_rst_vif.set_freq_mhz(IO_DIV4_FREQ_MHZ);
    cfg.main_clk_rst_vif.set_freq_mhz(MAIN_FREQ_MHZ);
    cfg.usb_clk_rst_vif.set_freq_mhz(USB_FREQ_MHZ);
  endtask

endclass : rstmgr_base_vseq
