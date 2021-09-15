// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Auxiliary class to deal with divided clocks. It predicts the divided clocks depending
// on whether the clock is divided as usual (step up), or if one division is undone (step
// down).
//
// The internal div2 clock is always running, and step down means we select the base
// clk_io instead of the internal clock.
//
// The div4 clock is handled differently: we internally maintain both a max and cnt. In
// normal operation the max is 1, so the div4 clock flips every two cycles; when stepped down
// the max is set to 0, so the clock flips every clk_io cycle.
class clock_dividers;

  // Step down means undo one clock divide: runs faster, as in "step down on the gas".
  typedef enum {
    DivStepDown,
    DivStepUp
  } div_step_e;
  typedef enum {
    Div2SelDiv2,
    Div2SelIo
  } div2_sel_e;

  // The internal div2 clock, always running.
  local bit        clk_io_div2     = 1'b0;
  // This selects the io clock when stepped down.
  local div2_sel_e div2_sel        = Div2SelDiv2;
  // The predicted div4 clock.
  local bit        clk_io_div4     = 1'b0;
  // The maximum value of cnt: becomes 0 when stepped down.
  local bit        clk_io_div4_max = 1;
  local bit        cnt             = 0;

  function new();
    reset();
  endfunction

  function void reset();
    clk_io_div2 = 1'b0;
    div2_sel = Div2SelDiv2;
    clk_io_div4 = 1'b0;
    clk_io_div4_max = 1;
    cnt = 0;
  endfunction

  function void increment_div2();
    clk_io_div2 = ~clk_io_div2;
  endfunction

  function void increment_div4(bit in_scan_mode);
    bit real_limit = in_scan_mode ? 1 : clk_io_div4_max;
    if (cnt < real_limit) begin
      cnt++;
    end else begin
      clk_io_div4 = ~clk_io_div4;
      cnt = 0;
    end
  endfunction

  function void step_div4(div_step_e step);
    if (step == DivStepUp) clk_io_div4_max = 1;
    else clk_io_div4_max = 0;
  endfunction

  function void step_div2(div_step_e step);
    if (step == DivStepUp) div2_sel = Div2SelDiv2;
    else div2_sel = Div2SelIo;
  endfunction

  function string show();
    return $sformatf(
        "clk_div2=%b div2_sel=%0s clk_div4=%b cnt=%b max=%b",
        clk_io_div2,
        div2_sel.name,
        clk_io_div4,
        cnt,
        clk_io_div4_max
    );
  endfunction

  function bit get_div2_clk(bit actual_clk_io);
    return div2_sel == Div2SelIo ? actual_clk_io : clk_io_div2;
  endfunction

  function bit get_div4_clk();
    return clk_io_div4;
  endfunction
endclass : clock_dividers

class clkmgr_scoreboard extends cip_base_scoreboard #(
  .CFG_T(clkmgr_env_cfg),
  .RAL_T(clkmgr_reg_block),
  .COV_T(clkmgr_env_cov)
);
  `uvm_component_utils(clkmgr_scoreboard)

  // local variables

  // TLM agent fifos

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      monitor_ast_clk_byp();
      monitor_div4_peri_clock();
      monitor_div2_peri_clock();
      monitor_io_peri_clock();
      monitor_usb_peri_clock();
      for (int i = 0; i < NUM_TRANS; ++i) begin
        fork
          automatic int trans_index = i;
          monitor_trans_clock(trans_index);
        join_none
      end
      monitor_clk_dividers();
      monitor_jitter_en();
    join_none
  endtask

  // Notice no check is done if the condition is 'X.
  function void check_clock(string clock_name, logic gating_condition, logic gated_clock);
    if (gating_condition === 1'b1) begin : check_clock_enabled
      if (!gated_clock) begin
        `uvm_error(`gfn, $sformatf("Peripheral %s clock should be enabled", clock_name))
      end
    end
    if (gating_condition === 1'b0) begin : check_clock_disabled
      if (gated_clock) begin
        `uvm_error(`gfn, $sformatf("Peripheral %s clock should be disabled", clock_name))
      end
    end
  endfunction

  // Clock monitors.
  // Notice the clock gating condition is sampled at the clock edge from clocking blocks,
  // but we add a #0 before the actual clock is checked. This is to be certain the clock
  // has assumed its value in case some logic needs to settle.

  task monitor_div4_peri_clock();
    forever
      @cfg.clkmgr_vif.peri_div4_cb begin
        if (cfg.io_clk_rst_vif.rst_n) begin
          logic enable = cfg.clkmgr_vif.peri_div4_cb.clk_enable;
          logic clk_en = cfg.clkmgr_vif.peri_div4_cb.ip_clk_en;
          logic scan_en = cfg.clkmgr_vif.scanmode_i == lc_ctrl_pkg::On;
          logic gating_condition = enable && clk_en || scan_en;
          #0;
          check_clock("div4", gating_condition, cfg.clkmgr_vif.clocks_o.clk_io_div4_peri);
          if (cfg.en_cov) begin
            cov.peri_cg_wrap[PeriDiv4].sample(enable, clk_en, scan_en);
          end
        end
      end
  endtask

  task monitor_div2_peri_clock();
    forever
      @cfg.clkmgr_vif.peri_div2_cb begin
        if (cfg.io_clk_rst_vif.rst_n) begin
          logic enable = cfg.clkmgr_vif.peri_div2_cb.clk_enable;
          logic clk_en = cfg.clkmgr_vif.peri_div2_cb.ip_clk_en;
          logic scan_en = cfg.clkmgr_vif.scanmode_i == lc_ctrl_pkg::On;
          logic gating_condition = enable && clk_en || scan_en;
          #0;
          check_clock("div2", gating_condition, cfg.clkmgr_vif.clocks_o.clk_io_div2_peri);
          if (cfg.en_cov) begin
            cov.peri_cg_wrap[PeriDiv2].sample(enable, clk_en, scan_en);
          end
        end
      end
  endtask

  task monitor_io_peri_clock();
    forever
      @cfg.clkmgr_vif.peri_io_cb begin
        if (cfg.io_clk_rst_vif.rst_n) begin
          logic enable = cfg.clkmgr_vif.peri_io_cb.clk_enable;
          logic clk_en = cfg.clkmgr_vif.peri_io_cb.ip_clk_en;
          logic scan_en = cfg.clkmgr_vif.scanmode_i == lc_ctrl_pkg::On;
          logic gating_condition = enable && clk_en || scan_en;
          #0;
          check_clock("io", gating_condition, cfg.clkmgr_vif.clocks_o.clk_io_peri);
          if (cfg.en_cov) begin
            cov.peri_cg_wrap[PeriIo].sample(enable, clk_en, scan_en);
          end
        end
      end
  endtask

  task monitor_usb_peri_clock();
    forever
      @cfg.clkmgr_vif.peri_usb_cb begin
        if (cfg.usb_clk_rst_vif.rst_n) begin
          logic enable = cfg.clkmgr_vif.peri_usb_cb.clk_enable;
          logic clk_en = cfg.clkmgr_vif.peri_usb_cb.ip_clk_en;
          logic scan_en = cfg.clkmgr_vif.scanmode_i == lc_ctrl_pkg::On;
          logic gating_condition = enable && clk_en || scan_en;
          #0;
          check_clock("usb", gating_condition, cfg.clkmgr_vif.clocks_o.clk_usb_peri);
          if (cfg.en_cov) begin
            cov.peri_cg_wrap[PeriUsb].sample(enable, clk_en, scan_en);
          end
        end
      end
  endtask

  task monitor_trans_clock(int trans_index);
    trans_e trans = trans_e'(trans_index);
    src_e   src = cfg.trans_to_src[trans];

    forever begin
      logic hint, idle, clk_en, scan_en, src_rst_n, gating_condition;

      // Wait for the correct clocking block (to ensure that we sample when the output clock should
      // be high if enabled), then read the relevant signals from that clocking block.
      case (src)
        SrcMain: begin
          @(cfg.clkmgr_vif.trans_cb);
          hint = cfg.clkmgr_vif.trans_cb.clk_hints[trans_index];
          idle = cfg.clkmgr_vif.trans_cb.idle_i[trans_index];
          clk_en = cfg.clkmgr_vif.trans_cb.ip_clk_en;
          src_rst_n = cfg.main_clk_rst_vif.rst_n;
        end
        SrcIoDiv4: begin
          @(cfg.clkmgr_vif.peri_div4_cb);
          hint = cfg.clkmgr_vif.peri_div4_cb.clk_hint_otbn;
          idle = cfg.clkmgr_vif.peri_div4_cb.otbn_idle;
          clk_en = cfg.clkmgr_vif.peri_div4_cb.ip_clk_en;
          src_rst_n = cfg.io_clk_rst_vif.rst_n;
        end
      endcase
      if (src_rst_n) begin
        scan_en = cfg.clkmgr_vif.scanmode_i == lc_ctrl_pkg::On;
        gating_condition = (hint || !idle) && clk_en || scan_en;

        #0;
        case (trans)
          TransAes: begin
            check_clock(trans.name(), gating_condition, cfg.clkmgr_vif.clocks_o.clk_main_aes);
          end
          TransHmac: begin
            check_clock(trans.name(), gating_condition, cfg.clkmgr_vif.clocks_o.clk_main_hmac);
          end
          TransKmac: begin
            check_clock(trans.name(), gating_condition, cfg.clkmgr_vif.clocks_o.clk_main_kmac);
          end
          TransOtbnIoDiv4: begin
            check_clock(trans.name(), gating_condition, cfg.clkmgr_vif.clocks_o.clk_io_div4_otbn);
          end
          TransOtbnMain: begin
            check_clock(trans.name(), gating_condition, cfg.clkmgr_vif.clocks_o.clk_main_otbn);
          end
        endcase
        if (cfg.en_cov) begin
          cov.trans_cg_wrap[trans].sample(hint, clk_en, scan_en, idle);
        end
      end
    end
  endtask

  task monitor_ast_clk_byp();
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
          if (((cfg.clkmgr_vif.clk_cb.extclk_ctrl_csr_sel == On) &&
               (cfg.clkmgr_vif.clk_cb.lc_dft_en_i == On)) ||
              (cfg.clkmgr_vif.clk_cb.lc_clk_byp_req == On)) begin
            `DV_CHECK_EQ(cfg.clkmgr_vif.ast_clk_byp_req, On, "Expected ast_clk_byp_req to be On")
          end
          if (cfg.en_cov) begin
            cov.extclk_cg.sample(cfg.clkmgr_vif.clk_cb.extclk_ctrl_csr_sel,
                                 cfg.clkmgr_vif.clk_cb.lc_dft_en_i,
                                 cfg.clkmgr_vif.clk_cb.lc_clk_byp_req, cfg.clkmgr_vif.scanmode_i);
          end
        end
      end
  endtask

  task monitor_clk_dividers();
    clock_dividers dividers = new();
    clock_dividers::div_step_e prev_div_step = clock_dividers::DivStepUp;
    // This controls the window for checking divided clocks. We open it after the
    // first increment, and close it upon reset. Needed for tests that reset.
    // May not be needed anymore since we reset the expected activity on reset
    // active.
    bit ok_to_check_dividers = 1'b0;

    #1;
    cfg.io_clk_rst_vif.wait_for_reset();
    fork
      forever
        @(negedge cfg.io_clk_rst_vif.rst_n) begin : handle_dividers_reset_start
          ok_to_check_dividers = 1'b0;
        end
      forever
        @(posedge cfg.io_clk_rst_vif.rst_n) begin : handle_dividers_reset_done
          dividers.reset();
          `uvm_info(`gfn, $sformatf("Reset divided clocks: %0s", dividers.show()), UVM_MEDIUM)
        end
      forever
        @cfg.clkmgr_vif.clk_cb begin : handle_divider_step_change
          clock_dividers::div_step_e div_step;
          bit step_down = cfg.clkmgr_vif.clk_cb.step_down;
          #0;

          step_down &= (cfg.clkmgr_vif.scanmode_i != On);
          div_step = step_down ? clock_dividers::DivStepDown : clock_dividers::DivStepUp;
          if (div_step != prev_div_step) begin
            `uvm_info(`gfn, $sformatf("Got a %0s request", div_step.name), UVM_LOW)
            dividers.step_div4(div_step);
            prev_div_step = div_step;
            @(negedge cfg.clkmgr_vif.clocks_o.clk_io_powerup) begin
              // Reconsider scanmode_i since it is asynchronous.
              dividers.step_div2(
                  step_down && (cfg.clkmgr_vif.scanmode_i != On) ?
                  clock_dividers::DivStepDown : clock_dividers::DivStepUp);
            end
            `uvm_info(`gfn, $sformatf("Stepped divided clocks: %0s", dividers.show()), UVM_HIGH)
          end
        end
      // Compare divided clocks, always based on values from clocking block (thus preponed).
      forever
        @cfg.clkmgr_vif.div_clks_cb begin : check_clocks
          if (cfg.io_clk_rst_vif.rst_n && ok_to_check_dividers) begin
            `DV_CHECK_EQ(cfg.clkmgr_vif.div_clks_cb.actual_clk_io_div4,
                         cfg.clkmgr_vif.div_clks_cb.exp_clk_io_div4, $sformatf(
                         "Mismatch for clk_io_div4_powerup, expected %b, got %b",
                         cfg.clkmgr_vif.div_clks_cb.exp_clk_io_div4,
                         cfg.clkmgr_vif.div_clks_cb.actual_clk_io_div4
                         ))
            `DV_CHECK_EQ(cfg.clkmgr_vif.div_clks_cb.actual_clk_io_div2,
                         cfg.clkmgr_vif.div_clks_cb.exp_clk_io_div2, $sformatf(
                         "Mismatch for clk_io_div2_powerup, expected %b, got %b",
                         cfg.clkmgr_vif.div_clks_cb.exp_clk_io_div2,
                         cfg.clkmgr_vif.div_clks_cb.actual_clk_io_div2
                         ))
          end
        end
      forever
        @(posedge cfg.clkmgr_vif.clocks_o.clk_io_powerup) begin : increment_clocks
          if (cfg.io_clk_rst_vif.rst_n) begin
            bit in_scan_mode = cfg.clkmgr_vif.scanmode_i == On;
            #0;
            // Deal with div4 update, accounting for scanmode's asynchronicity.
            // The incremented clock will be useful for the next comparison cycle.
            dividers.increment_div4(in_scan_mode);
            dividers.increment_div2();
            `uvm_info(`gfn, $sformatf("Incremented divided clocks: %0s", dividers.show()), UVM_HIGH)
            `uvm_info(`gfn, $sformatf(
                      "Update for div clk cb: div2 exp=%b, actual=%b, div4 exp=%b, actual=%b",
                      dividers.get_div2_clk(
                          cfg.clkmgr_vif.clocks_o.clk_io_powerup
                      ),
                      cfg.clkmgr_vif.clocks_o.clk_io_div2_powerup,
                      dividers.get_div4_clk(),
                      cfg.clkmgr_vif.clocks_o.clk_io_div4_powerup
                      ), UVM_HIGH)
            // This delay seems to help with xcelium: without it the actual divided clocks are stale.
            #1;
            cfg.clkmgr_vif.update_exp_clk_io_divs(
                .exp_div2_value(dividers.get_div2_clk(cfg.clkmgr_vif.clocks_o.clk_io_powerup)),
                .actual_div2_value(cfg.clkmgr_vif.clocks_o.clk_io_div2_powerup),
                .exp_div4_value(dividers.get_div4_clk()),
                .actual_div4_value(cfg.clkmgr_vif.clocks_o.clk_io_div4_powerup));
            if (ok_to_check_dividers == 1'b0) begin
              ok_to_check_dividers = 1'b1;
              `uvm_info(`gfn, "Ready to start checking divided clocks", UVM_LOW)
            end
          end else begin
            `uvm_info(`gfn, "Clearing expectations because io rst_n is active", UVM_LOW)
            // verilog_format: off  // the args are aligned to the function parenthesis
            cfg.clkmgr_vif.update_exp_clk_io_divs(
                .exp_div2_value(1'b0),
                .actual_div2_value(cfg.clkmgr_vif.clocks_o.clk_io_div2_powerup),
                .exp_div4_value(1'b0),
                .actual_div4_value(cfg.clkmgr_vif.clocks_o.clk_io_div4_powerup));
            // verilog_format: on
          end
        end
    join
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

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    bit            do_read_check = 1'b1;
    bit            write = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    bit            addr_phase_read = (!write && channel == AddrChannel);
    bit            addr_phase_write = (write && channel == AddrChannel);
    bit            data_phase_read = (!write && channel == DataChannel);
    bit            data_phase_write = (write && channel == DataChannel);

    string         access_str = write ? "write" : "read";
    string         channel_str = channel == AddrChannel ? "address" : "data";

    logic          extclk_ctrl_regwen = ral.extclk_ctrl_regwen.get_reset();

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
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
      "intr_state": begin
        // FIXME
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
        // FIXME
      end
      "extclk_ctrl_regwen": begin
        if (addr_phase_write) begin
          extclk_ctrl_regwen = item.a_data;
        end
      end
      "extclk_ctrl": begin
        if (addr_phase_write && extclk_ctrl_regwen) begin
          cfg.clkmgr_vif.update_extclk_ctrl(item.a_data);
        end
      end
      "jitter_enable": begin
        if (addr_phase_write) begin
          cfg.clkmgr_vif.update_jitter_enable(item.a_data);
        end
      end
      "clk_enables": begin
        if (addr_phase_write) begin
          cfg.clkmgr_vif.update_clk_enables(item.a_data);
        end
      end
      "clk_hints": begin
        // Clearing a hint sets an expectation for the status to transition to zero.
        if (addr_phase_write) begin
          cfg.clkmgr_vif.update_clk_hints(item.a_data);
        end
      end
      "clk_hints_status": begin
        // The status will respond to the hint once the target unit is idle. We check it in
        // the sequence.
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
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
