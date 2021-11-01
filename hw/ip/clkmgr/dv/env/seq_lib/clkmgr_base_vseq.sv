// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class clkmgr_base_vseq extends cip_base_vseq #(
  .RAL_T              (clkmgr_reg_block),
  .CFG_T              (clkmgr_env_cfg),
  .COV_T              (clkmgr_env_cov),
  .VIRTUAL_SEQUENCER_T(clkmgr_virtual_sequencer)
);
  `uvm_object_utils(clkmgr_base_vseq)

  // The extra cycles to wait after reset before starting any test, required so some CSRs (notably
  // hints_status) are properly set when inputs go through synchronizers.
  localparam int POST_APPLY_RESET_CYCLES = 10;

  // This delay in io_clk cycles is needed to allow updates to the hints_status CSR to go through
  // synchronizers.
  localparam int IO_DIV4_SYNC_CYCLES = 8;

  typedef enum {
    LcTxTSelOn,
    LcTxTSelOff,
    LcTxTSelOther
  } lc_tx_t_sel_e;

  // This simplifies the constraint blocks.
  function lc_tx_t get_lc_tx_t_from_sel(lc_tx_t_sel_e sel, lc_tx_t other);
    case (sel)
      LcTxTSelOn: return On;
      LcTxTSelOff: return Off;
      LcTxTSelOther: return other;
    endcase
  endfunction

  rand bit ip_clk_en;
  rand bit usb_clk_en_active;

  // This is used to detect a transition. Initialized to 1 since it only matters when
  // it drops.
  bit      prev_usb_clk_en_active = 1'b1;

  // This constraint is a workaround for https://github.com/lowRISC/opentitan/issues/6504.
  // TODO(maturana) Remove this constraint when the issue above is fixed.
  constraint usb_clk_en_active_c {usb_clk_en_active == 1'b1;}

  rand bit [NUM_TRANS-1:0] idle;

  // scanmode is set according to sel_scanmode, which is randomized with weights.
  lc_tx_t                  scanmode;
  rand lc_tx_t             scanmode_other;
  rand lc_tx_t_sel_e       sel_scanmode;
  int                      scanmode_on_weight = 8;

  constraint scanmode_c {
    sel_scanmode dist {
      LcTxTSelOn    := scanmode_on_weight,
      LcTxTSelOff   := 4,
      LcTxTSelOther := 4
    };
    !(scanmode_other inside {On, Off});
  }

  // extclk_ctrl_sel is set according to sel_extclk_ctrl_sel, which is randomized with weights.
  lc_tx_t            extclk_ctrl_sel;
  rand lc_tx_t       extclk_ctrl_sel_other;
  rand lc_tx_t_sel_e sel_extclk_ctrl_sel;

  constraint extclk_ctrl_sel_c {
    sel_extclk_ctrl_sel dist {
      LcTxTSelOn    := 4,
      LcTxTSelOff   := 2,
      LcTxTSelOther := 2
    };
    !(extclk_ctrl_sel_other inside {On, Off});
  }

  `uvm_object_new

  function void post_randomize();
    super.post_randomize();
    scanmode = get_lc_tx_t_from_sel(sel_scanmode, scanmode_other);
    extclk_ctrl_sel = get_lc_tx_t_from_sel(sel_extclk_ctrl_sel, extclk_ctrl_sel_other);
  endfunction

  virtual function void set_scanmode_on_low_weight();
    scanmode_on_weight = 2;
  endfunction

  task initialize_on_start();
    idle = '1;
    scanmode = Off;
    cfg.clkmgr_vif.init(.idle(idle), .scanmode(scanmode), .lc_dft_en(Off));
    ip_clk_en = 1'b1;
    usb_clk_en_active = 1'b1;
    control_ip_clocks();
  endtask

  task pre_start();
    update_csrs_with_reset_values();
    cfg.clkmgr_vif.init(.idle('1), .scanmode(scanmode), .lc_dft_en(Off));
    cfg.clkmgr_vif.update_ip_clk_en(1'b0);
    clkmgr_init();
    super.pre_start();
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
  endtask

  virtual task dut_shutdown();
    // check for pending clkmgr operations and wait for them to complete
    // TODO
  endtask

  task start_aon_clk();
    // This makes it so the aon clock starts without waiting for its reset,
    // and we won't need to call apply_reset for it.
    #1ps;
    cfg.aon_clk_rst_vif.drive_rst_pin(1'b0);
  endtask

  // This turns on or off the actual input clocks, as the pwrmgr would.
  // It pessimistically turning all clocks off on falling transitions,
  // and can be configured to keep the usb clk off on rising transitions.
  task control_ip_clocks();
    // Do nothing if nothing interesting changed.
    if (cfg.clkmgr_vif.pwr_i.ip_clk_en == ip_clk_en &&
        (!ip_clk_en || (usb_clk_en_active == prev_usb_clk_en_active)))
      return;
    `uvm_info(`gfn, $sformatf(
              "controlling clocks with ip_clk_en=%b usb_clk_en_active=%b",
              ip_clk_en,
              usb_clk_en_active
              ), UVM_LOW)
    if (!ip_clk_en) begin
      cfg.clkmgr_vif.pwr_i.ip_clk_en = ip_clk_en;
      @(negedge cfg.clkmgr_vif.pwr_o.clk_status);
      cfg.io_clk_rst_vif.stop_clk();
      cfg.main_clk_rst_vif.stop_clk();
      cfg.usb_clk_rst_vif.stop_clk();
      `uvm_info(`gfn, "stopped clocks", UVM_MEDIUM)
    end else begin
      cfg.io_clk_rst_vif.start_clk();
      cfg.main_clk_rst_vif.start_clk();
      if (usb_clk_en_active) cfg.usb_clk_rst_vif.start_clk();
      prev_usb_clk_en_active = usb_clk_en_active;
      `uvm_info(`gfn, "started clocks", UVM_MEDIUM)
      cfg.clkmgr_vif.pwr_i.ip_clk_en = ip_clk_en;
      @(posedge cfg.clkmgr_vif.pwr_o.clk_status);
    end
    `uvm_info(`gfn, "controlling clocks done", UVM_LOW)
  endtask

  virtual task apply_reset(string kind = "HARD");
    fork
      super.apply_reset(kind);
      if (kind == "HARD")
        fork
          cfg.aon_clk_rst_vif.apply_reset();
          cfg.main_clk_rst_vif.apply_reset();
          cfg.io_clk_rst_vif.apply_reset();
          cfg.usb_clk_rst_vif.apply_reset();
        join
    join
    initialize_on_start();
  endtask

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    int clk_periods_q[$] = {
      reset_duration_ps,
      cfg.main_clk_rst_vif.clk_period_ps,
      cfg.io_clk_rst_vif.clk_period_ps,
      cfg.usb_clk_rst_vif.clk_period_ps
    };
    reset_duration_ps = max(clk_periods_q);

    cfg.main_clk_rst_vif.drive_rst_pin(0);
    cfg.io_clk_rst_vif.drive_rst_pin(0);
    cfg.usb_clk_rst_vif.drive_rst_pin(0);

    super.apply_resets_concurrently(reset_duration_ps);

    cfg.main_clk_rst_vif.drive_rst_pin(1);
    cfg.io_clk_rst_vif.drive_rst_pin(1);
    cfg.usb_clk_rst_vif.drive_rst_pin(1);
  endtask

  task post_apply_reset(string reset_kind = "HARD");
    super.post_apply_reset(reset_kind);
    cfg.io_clk_rst_vif.wait_clks(POST_APPLY_RESET_CYCLES);
  endtask

  // setup basic clkmgr features
  virtual task clkmgr_init();
    // Initialize input clock frequencies.
    cfg.main_clk_rst_vif.set_freq_mhz((1.0 * MainClkHz) / 1_000_000);
    cfg.io_clk_rst_vif.set_freq_mhz((1.0 * IoClkHz) / 1_000_000);
    cfg.usb_clk_rst_vif.set_freq_mhz((1.0 * UsbClkHz) / 1_000_000);
    // The real clock rate for aon is 200kHz, but that can slow testing down.
    // Increasing its frequency improves DV efficiency without compromising quality.
    cfg.aon_clk_rst_vif.set_freq_mhz((1.0 * FakeAonClkHz) / 1_000_000);
  endtask

  function void update_csrs_with_reset_values();
    cfg.clkmgr_vif.update_clk_enables(ral.clk_enables.get_reset());
    cfg.clkmgr_vif.update_clk_hints(ral.clk_hints.get_reset());
    cfg.clkmgr_vif.update_extclk_ctrl(ral.extclk_ctrl.get_reset());
  endfunction

endclass : clkmgr_base_vseq
