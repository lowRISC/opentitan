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
  // This function is used for 2 enum mubi4_t and lc_tx_t. Use bit[3:0], so that we can skip type
  // casting when using this function
  function bit[3:0] get_lc_tx_t_from_sel(lc_tx_t_sel_e sel, bit[3:0] other);
    case (sel)
      LcTxTSelOn: return On;
      LcTxTSelOff: return Off;
      LcTxTSelOther: return other;
    endcase
  endfunction

  rand bit                 io_ip_clk_en;
  rand bit                 main_ip_clk_en;
  rand bit                 usb_ip_clk_en;

  rand bit [NUM_TRANS-1:0] idle;

  // scanmode is set according to sel_scanmode, which is randomized with weights.
  prim_mubi_pkg::mubi4_t   scanmode;
  rand bit [3:0]           scanmode_other;
  rand lc_tx_t_sel_e       sel_scanmode;
  int                      scanmode_on_weight = 8;

  constraint scanmode_c {
    sel_scanmode dist {
      LcTxTSelOn    := scanmode_on_weight,
      LcTxTSelOff   := 4,
      LcTxTSelOther := 4
    };
    !(scanmode_other inside {prim_mubi_pkg::MuBi4True, prim_mubi_pkg::MuBi4False});
  }

  // extclk_ctrl_sel is set according to sel_extclk_ctrl_sel, which is randomized with weights.
  lc_tx_t            extclk_ctrl_sel;
  rand bit [3:0]     extclk_ctrl_sel_other;
  rand lc_tx_t_sel_e sel_extclk_ctrl_sel;

  // TODO, consider to use macro DV_MUBI4_DIST
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
    scanmode = prim_mubi_pkg::MuBi4False;
    cfg.clkmgr_vif.init(.idle(idle), .scanmode(scanmode), .lc_dft_en(Off));
    io_ip_clk_en   = 1'b1;
    main_ip_clk_en = 1'b1;
    usb_ip_clk_en  = 1'b1;
    control_ip_clocks();
  endtask

  task pre_start();
    update_csrs_with_reset_values();
    cfg.clkmgr_vif.init(.idle('1), .scanmode(scanmode), .lc_dft_en(Off));
    cfg.clkmgr_vif.update_io_ip_clk_en(1'b0);
    cfg.clkmgr_vif.update_main_ip_clk_en(1'b0);
    cfg.clkmgr_vif.update_usb_ip_clk_en(1'b0);
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
  task control_ip_clocks();
    fork
      control_io_ip_clock();
      control_main_ip_clock();
      control_usb_ip_clock();
    join
  endtask

  task control_io_ip_clock();
    // Do nothing if nothing interesting changed.
    if (cfg.clkmgr_vif.pwr_i.io_ip_clk_en == io_ip_clk_en) return;
    `uvm_info(`gfn, $sformatf("controlling io clock with clk_en=%b", io_ip_clk_en), UVM_LOW)
    if (!io_ip_clk_en) begin
      cfg.clkmgr_vif.pwr_i.io_ip_clk_en = io_ip_clk_en;
      @(negedge cfg.clkmgr_vif.pwr_o.io_status);
      cfg.io_clk_rst_vif.stop_clk();
    end else begin
      cfg.io_clk_rst_vif.start_clk();
      cfg.clkmgr_vif.pwr_i.io_ip_clk_en = io_ip_clk_en;
      @(posedge cfg.clkmgr_vif.pwr_o.io_status);
    end
    `uvm_info(`gfn, "controlling io clock done", UVM_LOW)
  endtask

  task control_main_ip_clock();
    // Do nothing if nothing interesting changed.
    if (cfg.clkmgr_vif.pwr_i.main_ip_clk_en == main_ip_clk_en) return;
    `uvm_info(`gfn, $sformatf("controlling main clock with clk_en=%b", main_ip_clk_en), UVM_LOW)
    if (!main_ip_clk_en) begin
      cfg.clkmgr_vif.pwr_i.main_ip_clk_en = main_ip_clk_en;
      @(negedge cfg.clkmgr_vif.pwr_o.main_status);
      cfg.main_clk_rst_vif.stop_clk();
    end else begin
      cfg.main_clk_rst_vif.start_clk();
      cfg.clkmgr_vif.pwr_i.main_ip_clk_en = main_ip_clk_en;
      @(posedge cfg.clkmgr_vif.pwr_o.main_status);
    end
    `uvm_info(`gfn, "controlling main clock done", UVM_LOW)
  endtask

  task control_usb_ip_clock();
    // Do nothing if nothing interesting changed.
    if (cfg.clkmgr_vif.pwr_i.usb_ip_clk_en == usb_ip_clk_en) return;
    `uvm_info(`gfn, $sformatf("controlling usb clock with clk_en=%b", usb_ip_clk_en), UVM_LOW)
    if (!usb_ip_clk_en) begin
      cfg.clkmgr_vif.pwr_i.usb_ip_clk_en = usb_ip_clk_en;
      @(negedge cfg.clkmgr_vif.pwr_o.usb_status);
      cfg.usb_clk_rst_vif.stop_clk();
    end else begin
      cfg.usb_clk_rst_vif.start_clk();
      cfg.clkmgr_vif.pwr_i.usb_ip_clk_en = usb_ip_clk_en;
      @(posedge cfg.clkmgr_vif.pwr_o.usb_status);
    end
    `uvm_info(`gfn, "controlling usb clock done", UVM_LOW)
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
