// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class clkmgr_base_vseq extends cip_base_vseq #(
  .RAL_T              (clkmgr_reg_block),
  .CFG_T              (clkmgr_env_cfg),
  .COV_T              (clkmgr_env_cov),
  .VIRTUAL_SEQUENCER_T(clkmgr_virtual_sequencer)
);
  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  `uvm_object_utils(clkmgr_base_vseq)

  `uvm_object_new

  // The extra cycles to wait after reset before starting any test, required so some CSRs (notably
  // hints_status) are properly set when inputs go through synchronizers.
  localparam int POST_APPLY_RESET_CYCLES = 10;

  // This delay in io_clk cycles is needed to allow updates to the hints_status CSR to go through
  // synchronizers.
  localparam int IO_DIV4_SYNC_CYCLES = 8;

  rand bit         io_ip_clk_en;
  rand bit         main_ip_clk_en;
  rand bit         usb_ip_clk_en;

  rand hintables_t idle;

  mubi4_t          scanmode;
  int              scanmode_on_weight         = 8;

  lc_tx_t          extclk_ctrl_low_speed_sel;
  lc_tx_t          extclk_ctrl_sel;

  virtual function void set_scanmode_on_low_weight();
    scanmode_on_weight = 2;
  endfunction

  function void post_randomize();
    extclk_ctrl_low_speed_sel = get_rand_lc_tx_val(6, 2, 2);
    extclk_ctrl_sel = get_rand_lc_tx_val(4, 2, 2);
    scanmode = get_rand_mubi4_val(scanmode_on_weight, 4, 4);
    `uvm_info(`gfn, $sformatf(
              "randomize gives extclk_ctrl_sel=0x%x, extclk_ctrl_low_speed_sel=0x%x, scanmode=0x%x",
              extclk_ctrl_sel,
              extclk_ctrl_low_speed_sel,
              scanmode
              ), UVM_MEDIUM)
    super.post_randomize();
  endfunction

  task initialize_on_start();
    `uvm_info(`gfn, "In clkmgr_if initialize_on_start", UVM_MEDIUM)
    idle = '1;
    scanmode = prim_mubi_pkg::MuBi4False;
    cfg.clkmgr_vif.init(.idle(idle), .scanmode(scanmode), .lc_debug_en(Off));
    io_ip_clk_en   = 1'b1;
    main_ip_clk_en = 1'b1;
    usb_ip_clk_en  = 1'b1;
    control_ip_clocks();
  endtask

  task pre_start();
    update_csrs_with_reset_values();
    cfg.clkmgr_vif.init(.idle('1), .scanmode(scanmode), .lc_debug_en(Off));
    cfg.clkmgr_vif.update_io_ip_clk_en(1'b0);
    cfg.clkmgr_vif.update_main_ip_clk_en(1'b0);
    cfg.clkmgr_vif.update_usb_ip_clk_en(1'b0);
    cfg.clkmgr_vif.update_all_clk_byp_ack(prim_mubi_pkg::MuBi4False);
    cfg.clkmgr_vif.update_io_clk_byp_ack(prim_mubi_pkg::MuBi4False);
    clkmgr_init();
    super.pre_start();
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
  endtask

  virtual task dut_shutdown();
    // check for pending clkmgr operations and wait for them to complete
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
      // There is a check that the RTL generates in a bounded number of cycles, so if this posedge
      // never occurs we wont timeout.
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

  task disable_frequency_measurement(clk_mesr_e which);
    `uvm_info(`gfn, $sformatf("Disabling frequency measurement for %0s", which.name), UVM_MEDIUM)
    case (which)
      ClkMesrIo: begin
        csr_wr(.ptr(ral.io_measure_ctrl.en), .value(0));
      end
      ClkMesrIoDiv2: begin
        csr_wr(.ptr(ral.io_div2_measure_ctrl.en), .value(0));
      end
      ClkMesrIoDiv4: begin
        csr_wr(.ptr(ral.io_div4_measure_ctrl.en), .value(0));
      end
      ClkMesrMain: begin
        csr_wr(.ptr(ral.main_measure_ctrl.en), .value(0));
      end
      ClkMesrUsb: begin
        csr_wr(.ptr(ral.usb_measure_ctrl.en), .value(0));
      end
      default: ;
    endcase
  endtask

  task enable_frequency_measurement(clk_mesr_e which, int min_threshold, int max_threshold);
    `uvm_info(`gfn, $sformatf(
              "Enabling frequency measurement for %0s, min=%0d, max=%0d, expected=%0d",
              which.name,
              min_threshold,
              max_threshold,
              ExpectedCounts[which]
              ), UVM_MEDIUM)
    case (which)
      ClkMesrIo: begin
        ral.io_measure_ctrl.en.set(1);
        ral.io_measure_ctrl.min_thresh.set(min_threshold);
        ral.io_measure_ctrl.max_thresh.set(max_threshold);
        csr_update(.csr(ral.io_measure_ctrl));
      end
      ClkMesrIoDiv2: begin
        ral.io_div2_measure_ctrl.en.set(1);
        ral.io_div2_measure_ctrl.min_thresh.set(min_threshold);
        ral.io_div2_measure_ctrl.max_thresh.set(max_threshold);
        csr_update(.csr(ral.io_div2_measure_ctrl));
      end
      ClkMesrIoDiv4: begin
        ral.io_div4_measure_ctrl.en.set(1);
        ral.io_div4_measure_ctrl.min_thresh.set(min_threshold);
        ral.io_div4_measure_ctrl.max_thresh.set(max_threshold);
        csr_update(.csr(ral.io_div4_measure_ctrl));
      end
      ClkMesrMain: begin
        ral.main_measure_ctrl.en.set(1);
        ral.main_measure_ctrl.min_thresh.set(min_threshold);
        ral.main_measure_ctrl.max_thresh.set(max_threshold);
        csr_update(.csr(ral.main_measure_ctrl));
      end
      ClkMesrUsb: begin
        ral.usb_measure_ctrl.en.set(1);
        ral.usb_measure_ctrl.min_thresh.set(min_threshold);
        ral.usb_measure_ctrl.max_thresh.set(max_threshold);
        csr_update(.csr(ral.usb_measure_ctrl));
      end
      default: ;
    endcase
  endtask

  task disturb_measured_clock(clk_mesr_e clk, bit enable);
    case (clk)
      ClkMesrIo, ClkMesrIoDiv2, ClkMesrIoDiv4:
      if (enable) cfg.io_clk_rst_vif.start_clk();
      else cfg.io_clk_rst_vif.stop_clk();
      ClkMesrMain:
      if (enable) cfg.main_clk_rst_vif.start_clk();
      else cfg.main_clk_rst_vif.stop_clk();
      ClkMesrUsb:
      if (enable) cfg.usb_clk_rst_vif.start_clk();
      else cfg.usb_clk_rst_vif.stop_clk();
      default: ;
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
               "Mismatch for %0s recoverable error, expected 0b%b, got 0x%b",
               error_type,
               expected,
               actual
               ))
  endfunction

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
