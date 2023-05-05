// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The scoreboard checks the jitter_an_o output, and processes CSR checks.
// It also samples most functional coverage groups.
class clkmgr_scoreboard extends cip_base_scoreboard #(
  .CFG_T(clkmgr_env_cfg),
  .RAL_T(clkmgr_reg_block),
  .COV_T(clkmgr_env_cov)
);
  `uvm_component_utils(clkmgr_scoreboard)

  // local variables
  logic extclk_ctrl_regwen;
  logic measure_ctrl_regwen;

  // TLM agent fifos

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    cfg.scoreboard = this;
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      monitor_all_clk_byp();
      monitor_io_clk_byp();
      monitor_jitter_en();
      sample_peri_covs();
      sample_trans_covs();
      sample_freq_measurement_covs();
      sample_fatal_err_cov();
      sample_recov_err_cov();
    join_none
  endtask

  task monitor_all_clk_byp();
    mubi4_t prev_all_clk_byp_req = MuBi4False;
    forever
      @cfg.clkmgr_vif.clk_cb begin
        if (cfg.clkmgr_vif.all_clk_byp_req != prev_all_clk_byp_req) begin
          `uvm_info(`gfn, $sformatf(
                    "Got all_clk_byp_req %s",
                    cfg.clkmgr_vif.all_clk_byp_req == MuBi4True ? "True" : "False"
                    ), UVM_MEDIUM)
          prev_all_clk_byp_req = cfg.clkmgr_vif.all_clk_byp_req;
        end
        if (cfg.clk_rst_vif.rst_n) begin
          if (cfg.en_cov) begin
            cov.extclk_cg.sample(cfg.clkmgr_vif.clk_cb.extclk_ctrl_csr_sel == MuBi4True,
                                 cfg.clkmgr_vif.clk_cb.extclk_ctrl_csr_step_down == MuBi4True,
                                 cfg.clkmgr_vif.clk_cb.lc_hw_debug_en_i == On,
                                 cfg.clkmgr_vif.clk_cb.lc_clk_byp_req == On,
                                 cfg.clkmgr_vif.scanmode_i == MuBi4True);
          end
        end
      end
  endtask

  task monitor_io_clk_byp();
    lc_tx_t prev_lc_clk_byp_req = Off;
    forever
      @cfg.clkmgr_vif.clk_cb begin
        if (cfg.clkmgr_vif.lc_clk_byp_req != prev_lc_clk_byp_req) begin
          `uvm_info(`gfn, $sformatf(
                    "Got lc_clk_byp_req %s", cfg.clkmgr_vif.lc_clk_byp_req == On ? "On" : "Off"),
                    UVM_MEDIUM)
          prev_lc_clk_byp_req = cfg.clkmgr_vif.lc_clk_byp_req;
        end
        if (cfg.clk_rst_vif.rst_n) begin
          if (cfg.en_cov) begin
            cov.extclk_cg.sample(cfg.clkmgr_vif.clk_cb.extclk_ctrl_csr_sel == MuBi4True,
                                 cfg.clkmgr_vif.clk_cb.extclk_ctrl_csr_step_down == MuBi4True,
                                 cfg.clkmgr_vif.clk_cb.lc_hw_debug_en_i == On,
                                 cfg.clkmgr_vif.clk_cb.lc_clk_byp_req == On,
                                 cfg.clkmgr_vif.scanmode_i == MuBi4True);
          end
        end
      end
  endtask

  task monitor_jitter_en();
    fork
      forever
        @cfg.clkmgr_vif.clk_cb begin
          if (cfg.clk_rst_vif.rst_n) begin
            @cfg.clkmgr_vif.jitter_enable_csr begin
              cfg.clk_rst_vif.wait_clks(2);
              `DV_CHECK_EQ(cfg.clkmgr_vif.jitter_en_o, cfg.clkmgr_vif.jitter_enable_csr,
                           "Mismatching jitter enable output")
            end
          end
        end
      forever
        @cfg.clkmgr_vif.clk_cb begin
          if (cfg.clk_rst_vif.rst_n) begin
            @cfg.clkmgr_vif.jitter_en_o begin
              cfg.clk_rst_vif.wait_clks(2);
              `DV_CHECK_EQ(cfg.clkmgr_vif.jitter_en_o, cfg.clkmgr_vif.jitter_enable_csr,
                           "Mismatching jitter enable output")
            end
          end
        end
    join
  endtask

  task sample_peri_covs();
    fork
      forever
        @cfg.clkmgr_vif.peri_io_cb begin
          if (cfg.io_clk_rst_vif.rst_n && cfg.en_cov) begin
            cov.peri_cg_wrap[PeriIo].sample(cfg.clkmgr_vif.peri_io_cb.clk_enable,
                                            cfg.clkmgr_vif.peri_io_cb.ip_clk_en,
                                            cfg.clkmgr_vif.scanmode_i == MuBi4True);
          end
        end
      forever
        @cfg.clkmgr_vif.peri_div2_cb begin
          if (cfg.io_clk_rst_vif.rst_n && cfg.en_cov) begin
            cov.peri_cg_wrap[PeriDiv2].sample(cfg.clkmgr_vif.peri_div2_cb.clk_enable,
                                              cfg.clkmgr_vif.peri_div2_cb.ip_clk_en,
                                              cfg.clkmgr_vif.scanmode_i == MuBi4True);
          end
        end
      forever
        @cfg.clkmgr_vif.peri_div4_cb begin
          if (cfg.io_clk_rst_vif.rst_n && cfg.en_cov) begin
            cov.peri_cg_wrap[PeriDiv4].sample(cfg.clkmgr_vif.peri_div4_cb.clk_enable,
                                              cfg.clkmgr_vif.peri_div4_cb.ip_clk_en,
                                              cfg.clkmgr_vif.scanmode_i == MuBi4True);
          end
        end
      forever
        @cfg.clkmgr_vif.peri_usb_cb begin
          if (cfg.io_clk_rst_vif.rst_n && cfg.en_cov) begin
            cov.peri_cg_wrap[PeriUsb].sample(cfg.clkmgr_vif.peri_usb_cb.clk_enable,
                                             cfg.clkmgr_vif.peri_usb_cb.ip_clk_en,
                                             cfg.clkmgr_vif.scanmode_i == MuBi4True);
          end
        end
    join
  endtask

  task sample_trans_cov(int trans_index);
    logic hint, clk_en, idle, src_rst_en;
    trans_e trans = trans_e'(trans_index);
    forever begin
      @cfg.clkmgr_vif.trans_cb;
      hint = cfg.clkmgr_vif.trans_cb.clk_hints[trans_index];
      idle = cfg.clkmgr_vif.trans_cb.idle_i[trans_index];
      clk_en = cfg.clkmgr_vif.trans_cb.ip_clk_en;
      src_rst_en = cfg.main_clk_rst_vif.rst_n;
      if (src_rst_en && cfg.en_cov) begin
        logic scan_en = cfg.clkmgr_vif.scanmode_i == prim_mubi_pkg::MuBi4True;
        cov.trans_cg_wrap[trans].sample(hint, clk_en, scan_en, idle);
      end
    end
  endtask

  task sample_trans_covs();
    for (int i = 0; i < $bits(hintables_t); ++i) begin
      fork
        automatic int trans_index = i;
        sample_trans_cov(trans_index);
      join_none
    end
  endtask

  local task sample_freq_measurement_cov(clk_mesr_e clk, ref freq_measurement_t measurement,
                                         logic timeout);
    if (cfg.en_cov) begin
      cov.freq_measure_cg_wrap[clk].sample(!measurement.slow && !measurement.fast, measurement.slow,
                                           measurement.fast, timeout);
      `uvm_info(`gfn, $sformatf(
                "Cov for %0s: %0s",
                clk.name(),
                measurement.slow ? "slow" : measurement.fast ? "fast" : "okay"
                ), UVM_MEDIUM)
      measurement = '{default: 0};
    end
  endtask

  task sample_freq_measurement_covs();
    fork
      forever
        @(posedge cfg.clkmgr_vif.io_freq_measurement.valid or posedge cfg.clkmgr_vif.io_timeout_err) begin
          sample_freq_measurement_cov(ClkMesrIo, cfg.clkmgr_vif.io_freq_measurement,
                                      cfg.clkmgr_vif.io_timeout_err);
        end

      forever
        @(posedge cfg.clkmgr_vif.io_div2_freq_measurement.valid or posedge cfg.clkmgr_vif.io_div2_timeout_err) begin
          sample_freq_measurement_cov(ClkMesrIoDiv2, cfg.clkmgr_vif.io_div2_freq_measurement,
                                      cfg.clkmgr_vif.io_div2_timeout_err);

        end
      forever
        @(posedge cfg.clkmgr_vif.io_div4_freq_measurement.valid or posedge cfg.clkmgr_vif.io_div4_timeout_err) begin
          sample_freq_measurement_cov(ClkMesrIoDiv4, cfg.clkmgr_vif.io_div4_freq_measurement,
                                      cfg.clkmgr_vif.io_div4_timeout_err);
        end
      forever
        @(posedge cfg.clkmgr_vif.main_freq_measurement.valid or posedge cfg.clkmgr_vif.main_timeout_err) begin
          sample_freq_measurement_cov(ClkMesrMain, cfg.clkmgr_vif.main_freq_measurement,
                                      cfg.clkmgr_vif.main_timeout_err);
        end
      forever
        @(posedge cfg.clkmgr_vif.usb_freq_measurement.valid or posedge cfg.clkmgr_vif.usb_timeout_err) begin
          sample_freq_measurement_cov(ClkMesrUsb, cfg.clkmgr_vif.usb_freq_measurement,
                                      cfg.clkmgr_vif.usb_timeout_err);
        end
    join_none
  endtask

  task sample_recov_err_cov();
    fork
      forever
        @cfg.clkmgr_csrs_vif.csrs_cb.recov_err_csr if (cfg.en_cov) begin
          cov.recov_err_cg.sample(
              cfg.clkmgr_csrs_vif.csrs_cb.recov_err_csr[10],
              cfg.clkmgr_csrs_vif.csrs_cb.recov_err_csr[9],
              cfg.clkmgr_csrs_vif.csrs_cb.recov_err_csr[8],
              cfg.clkmgr_csrs_vif.csrs_cb.recov_err_csr[7],
              cfg.clkmgr_csrs_vif.csrs_cb.recov_err_csr[6],
              cfg.clkmgr_csrs_vif.csrs_cb.recov_err_csr[5],
              cfg.clkmgr_csrs_vif.csrs_cb.recov_err_csr[4],
              cfg.clkmgr_csrs_vif.csrs_cb.recov_err_csr[3],
              cfg.clkmgr_csrs_vif.csrs_cb.recov_err_csr[2],
              cfg.clkmgr_csrs_vif.csrs_cb.recov_err_csr[1],
              cfg.clkmgr_csrs_vif.csrs_cb.recov_err_csr[0]);
          `uvm_info(`gfn, $sformatf(
                    "Recoverable errors sampled: 0x%x", cfg.clkmgr_csrs_vif.csrs_cb.recov_err_csr),
                    UVM_MEDIUM)
        end
    join_none
  endtask

  task sample_fatal_err_cov();
    fork
      forever
        @cfg.clkmgr_csrs_vif.csrs_cb.fatal_err_csr if (cfg.en_cov) begin
          cov.fatal_err_cg.sample(
              cfg.clkmgr_csrs_vif.csrs_cb.fatal_err_csr[2],
              cfg.clkmgr_csrs_vif.csrs_cb.fatal_err_csr[1],
              cfg.clkmgr_csrs_vif.csrs_cb.fatal_err_csr[0]);
          `uvm_info(`gfn, $sformatf(
                    "Fatal errors sampled: 0x%x", cfg.clkmgr_csrs_vif.csrs_cb.fatal_err_csr),
                    UVM_MEDIUM)
        end
    join_none
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    bit            do_read_check = 1'b1;
    bit            write = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit            addr_phase_read = (!write && channel == AddrChannel);
    bit            addr_phase_write = (write && channel == AddrChannel);
    bit            data_phase_read = (!write && channel == DataChannel);
    bit            data_phase_write = (write && channel == DataChannel);

    string         access_str = write ? "write" : "read";
    string         channel_str = channel == AddrChannel ? "address" : "data";

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // If incoming access is a write to a valid csr, update prediction right away.
    if (addr_phase_write) begin
      `uvm_info(`gfn, $sformatf("Writing 0x%0x to %s", item.a_data, csr.get_name()), UVM_MEDIUM)
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // Process the csr req:
    // - For write, update local variable and fifo at address phase.
    // - For read, update predication at address phase and compare at data phase.
    case (csr.get_name())
      // add individual case item for each csr
      "alert_test": begin
        // FIXME
      end
      "extclk_ctrl_regwen": begin
        if (addr_phase_write) extclk_ctrl_regwen = item.a_data;
      end
      "extclk_ctrl": begin
        typedef logic [2*$bits(prim_mubi_pkg::mubi4_t) - 1:0] extclk_ctrl_t;
        if (addr_phase_write && extclk_ctrl_regwen) begin
          `DV_CHECK_EQ(extclk_ctrl_t'(item.a_data), {
                       cfg.clkmgr_vif.extclk_ctrl_csr_step_down, cfg.clkmgr_vif.extclk_ctrl_csr_sel
                       })
        end
      end
      "extclk_status": begin
        do_read_check = 1'b0;
      end
      "jitter_regwen": begin
      end
      "jitter_enable": begin
        if (addr_phase_write && `gmv(ral.jitter_regwen)) begin
          `DV_CHECK_EQ(prim_mubi_pkg::mubi4_t'(item.a_data), cfg.clkmgr_vif.jitter_enable_csr)
        end
      end
      "clk_enables": begin
        if (addr_phase_write) begin
          `DV_CHECK_EQ(clk_enables_t'(item.a_data), cfg.clkmgr_vif.clk_enables_csr)
        end
      end
      "clk_hints": begin
        // Clearing a hint sets an expectation for the status to transition to zero.
        if (addr_phase_write) begin
          `DV_CHECK_EQ(clk_hints_t'(item.a_data), cfg.clkmgr_vif.clk_hints_csr)
        end
      end
      "clk_hints_status": begin
        // The status will respond to the hint once the target unit is idle. We check it in
        // the sequence.
        do_read_check = 1'b0;
      end
      "measure_ctrl_regwen": begin
        if (addr_phase_write) measure_ctrl_regwen = item.a_data;
      end
      "io_meas_ctrl_en": begin
      end
      "io_div2_meas_ctrl_en": begin
      end
      "io_div4_meas_ctrl_en": begin
      end
      "main_meas_ctrl_en": begin
      end
      "usb_meas_ctrl_en": begin
      end
      "io_meas_ctrl_shadowed": begin
      end
      "io_div2_meas_ctrl_shadowed": begin
      end
      "io_div4_meas_ctrl_shadowed": begin
      end
      "main_meas_ctrl_shadowed": begin
      end
      "usb_meas_ctrl_shadowed": begin
      end
      "recov_err_code": begin
        do_read_check = 1'b0;
      end
      "fatal_err_code": begin
        do_read_check = 1'b0;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      `uvm_info(`gfn, $sformatf("Reading 0x%0x from %s", item.d_data, csr.get_name()), UVM_MEDIUM)
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, $sformatf(
                     "reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    extclk_ctrl_regwen  = ral.extclk_ctrl_regwen.get_reset();
    measure_ctrl_regwen = ral.measure_ctrl_regwen.get_reset();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
