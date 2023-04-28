// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwrmgr_scoreboard extends cip_base_scoreboard #(
  .CFG_T(pwrmgr_env_cfg),
  .RAL_T(pwrmgr_reg_block),
  .COV_T(pwrmgr_env_cov)
);
  `uvm_component_utils(pwrmgr_scoreboard)

  // local variables

  // TLM agent fifos

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    string common_seq_type;
    super.build_phase(phase);

    void'($value$plusargs("run_%0s", common_seq_type));
    if (common_seq_type == "stress_all_with_rand_reset") do_alert_check = 0;
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    cfg.run_phase = phase;
    fork
      monitor_power_glitch();
      monitor_escalation_timeout();
      reset_cip_helper();
      wakeup_ctrl_coverage_collector();
      wakeup_intr_coverage_collector();
      low_power_coverage_collector();
      reset_coverage_collector();
      rom_coverage_collector();
    join_none
  endtask

  task monitor_power_glitch();
    fork
      forever
        @cfg.pwrmgr_vif.rst_main_n begin
          if (cfg.pwrmgr_vif.rst_main_n == 1'b0 && `gmv(ral.control.main_pd_n)) begin
            set_exp_alert("fatal_fault", 1, 500);
          end
        end
    join
  endtask

  // An escalation timeout is triggered in test sequences by stopping clk_esc_i or by driving
  // rst_esc_ni active when the dut state is not expecting it.
  task monitor_escalation_timeout();
    fork
      forever
        @(posedge cfg.esc_clk_rst_vif.clk_gate) begin
          if (cfg.pwrmgr_vif.pwr_ast_req.io_clk_en && cfg.pwrmgr_vif.pwr_clk_req.io_ip_clk_en) begin
            `uvm_info(`gfn, "Detected unexpected clk_esc_i stop", UVM_MEDIUM)
            set_exp_alert("fatal_fault", 1, 500);
          end
        end
      forever
        @(negedge cfg.esc_clk_rst_vif.o_rst_n) begin
          if (cfg.pwrmgr_vif.fetch_en == lc_ctrl_pkg::On) begin
            `uvm_info(`gfn, "Detected unexpected rst_esc_ni active", UVM_MEDIUM)
            set_exp_alert("fatal_fault", 1, 500);
          end
        end
    join
  endtask

  // We need to reset the cip scoreboard, since the alert handler responds
  // to lc domain0 resets, yet the pwrmgr's clk_rst_vif is aon. So when a
  // reset happens the cip scoreboard needs to be informed, both when reset
  // starts and when it ends.
  task reset_cip_helper();
    fork
      forever
        @cfg.pwrmgr_vif.pwr_rst_req.rst_lc_req begin
          if (|cfg.pwrmgr_vif.pwr_rst_req.rst_lc_req) begin
            // Start of d0 reset request.
            `uvm_info(`gfn, "pwrmgr start reset in reset_cip_helper", UVM_MEDIUM)
            cfg.under_reset = 1;
          end
        end
      forever
        @cfg.pwrmgr_vif.fetch_en begin
          if (cfg.pwrmgr_vif.fetch_en == lc_ctrl_pkg::On) begin
            // End of d0 reset request.
            `uvm_info(`gfn, "pwrmgr end reset in reset_cip_helper", UVM_MEDIUM)
            reset_alert_state();
          end
        end
    join
  endtask

  task wakeup_ctrl_coverage_collector();
    forever
      @(posedge (|cfg.pwrmgr_vif.wakeups_i)) begin
        if (cfg.en_cov) begin
          // Allow for synchronization delay.
          cfg.slow_clk_rst_vif.wait_clks(2);
          foreach (cov.wakeup_ctrl_cg_wrap[i]) begin
            cov.wakeup_ctrl_cg_wrap[i].sample(cfg.pwrmgr_vif.wakeup_en[i],
                                              cfg.pwrmgr_vif.wakeup_capture_en,
                                              cfg.pwrmgr_vif.wakeups_i[i]);
          end
        end
      end
  endtask

  task wakeup_intr_coverage_collector();
    forever
      @(posedge (cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateRomCheckDone)) begin
        if (cfg.en_cov) begin
          foreach (cov.wakeup_intr_cg_wrap[i]) begin
            cov.wakeup_intr_cg_wrap[i].sample(
                cfg.pwrmgr_vif.wakeup_status[i], cfg.pwrmgr_vif.intr_enable,
                cfg.pwrmgr_vif.intr_status, cfg.pwrmgr_vif.intr_wakeup);
          end
        end
      end
  endtask

  task low_power_coverage_collector();
    forever
      @(posedge cfg.pwrmgr_vif.pwr_rst_req.reset_cause == pwrmgr_pkg::LowPwrEntry) begin
        if (cfg.en_cov) begin
          // At this point pwrmgr is asleep.
          cov.control_cg.sample(control_enables, 1'b1);
        end
      end
  endtask

  local task sample_reset_coverage(bit sleep);
    cov.hw_reset_0_cg.sample(cfg.pwrmgr_vif.rstreqs_i[0], cfg.pwrmgr_vif.reset_en[0], sleep);
    cov.hw_reset_1_cg.sample(cfg.pwrmgr_vif.rstreqs_i[1], cfg.pwrmgr_vif.reset_en[1], sleep);
    cov.rstmgr_sw_reset_cg.sample(cfg.pwrmgr_vif.sw_rst_req_i == prim_mubi_pkg::MuBi4True);
    cov.main_power_reset_cg.sample(
        cfg.pwrmgr_vif.pwr_rst_req.rstreqs[pwrmgr_reg_pkg::ResetMainPwrIdx], sleep);
    cov.esc_reset_cg.sample(cfg.pwrmgr_vif.pwr_rst_req.rstreqs[pwrmgr_reg_pkg::ResetEscIdx], sleep);
    `uvm_info(`gfn, $sformatf(
              {
                "reset_cg sample with hw_resets=%b, hw_resets_en=%b, ",
                "esc_rst=%b, main_pwr_rst=%b, sw_rst=%b, sleep=%b"
              },
              cfg.pwrmgr_vif.rstreqs_i,
              cfg.pwrmgr_vif.reset_en,
              cfg.pwrmgr_vif.pwr_rst_req.rstreqs[pwrmgr_reg_pkg::ResetEscIdx],
              cfg.pwrmgr_vif.pwr_rst_req.rstreqs[pwrmgr_reg_pkg::ResetMainPwrIdx],
              cfg.pwrmgr_vif.sw_rst_req_i == prim_mubi_pkg::MuBi4True,
              sleep
              ), UVM_MEDIUM)
  endtask

  task reset_coverage_collector();
    fork
      forever
        @(posedge cfg.pwrmgr_vif.pwr_rst_req.reset_cause == pwrmgr_pkg::HwReq) begin
          if (cfg.en_cov) begin
            sample_reset_coverage(.sleep(1'b0));
          end
        end
      forever
        @(posedge cfg.pwrmgr_vif.slow_state == pwrmgr_pkg::SlowPwrStateLowPower) begin
          if (cfg.en_cov) begin
            sample_reset_coverage(.sleep(1'b1));
          end
        end
    join_none
  endtask

  task rom_coverage_collector();
    forever
      @(cfg.pwrmgr_vif.rom_ctrl or cfg.pwrmgr_vif.lc_hw_debug_en or cfg.pwrmgr_vif.lc_dft_en) begin
        if (cfg.en_cov) begin
          cov.rom_active_blockers_cg.sample(cfg.pwrmgr_vif.rom_ctrl.done,
                                            cfg.pwrmgr_vif.rom_ctrl.good, cfg.pwrmgr_vif.lc_dft_en,
                                            cfg.pwrmgr_vif.lc_hw_debug_en);
        end
      end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    bit            do_read_check = ~(cfg.disable_csr_rd_chk);
    bit            skip_intr_chk = cfg.invalid_st_test;
    bit            write = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit            addr_phase_read = (!write && channel == AddrChannel);
    bit            addr_phase_write = (write && channel == AddrChannel);
    bit            data_phase_read = (!write && channel == DataChannel);
    bit            data_phase_write = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      `uvm_info(`gfn, $sformatf("Writing 0x%x to %s", item.a_data, csr.get_full_name()), UVM_MEDIUM)
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        if (skip_intr_chk) return;
        if (data_phase_write) begin
          exp_intr &= ~item.a_data;
        end else if (data_phase_read) begin
          bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
          foreach (exp_intr[i]) begin
            if (cfg.en_cov) begin
              cov.intr_cg.sample(i, intr_en[i], exp_intr[i]);
              cov.intr_pins_cg.sample(i, cfg.intr_vif.pins[i]);
            end
            `DV_CHECK_EQ(item.d_data[i], exp_intr[i], $sformatf("Interrupt bit %0d", i));
            `DV_CHECK_CASE_EQ(cfg.intr_vif.pins[i], (intr_en[i] & exp_intr[i]), $sformatf(
                              "Interrupt_pin bit %0d", i));
          end
        end
        // rw1c: write 1 clears, write 0 is no-op.
        do_read_check = 1'b0;
      end
      "intr_enable", "alert_test": begin
        // Do nothing
      end
      "intr_test": begin
        if (data_phase_write) begin
          bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
          exp_intr |= item.a_data;
          if (cfg.en_cov) begin
            foreach (exp_intr[i]) begin
              cov.intr_test_cg.sample(i, item.a_data[i], intr_en[i], exp_intr[i]);
            end
          end
        end
        // Write-only, so it can't be read.
        do_read_check = 1'b0;
      end
      "ctrl_cfg_regwen": begin
        // Read-only. Hardware clears this bit when going to low power mode,
        // and sets it in active mode.
        do_read_check = 1'b0;
      end
      "control": begin
        // Only some bits can be checked on reads. Bit 0 is cleared by hardware
        // on low power transition or when registering a valid reset.
        if (data_phase_write) begin
          low_power_hint = get_field_val(ral.control.low_power_hint, item.a_data);
          control_enables = '{
              core_clk_en: get_field_val(ral.control.core_clk_en, item.a_data),
              io_clk_en: get_field_val(ral.control.io_clk_en, item.a_data),
              usb_clk_en_lp: get_field_val(ral.control.usb_clk_en_lp, item.a_data),
              usb_clk_en_active: get_field_val(ral.control.usb_clk_en_active, item.a_data),
              main_pd_n: get_field_val(ral.control.main_pd_n, item.a_data)
          };
          `uvm_info(`gfn, $sformatf("Writing low power hint=%b", low_power_hint), UVM_MEDIUM)
          `uvm_info(`gfn, $sformatf("Writing control_enables=%p", control_enables), UVM_MEDIUM)
          if (cfg.en_cov) begin
            // At this point the processor is not asleep.
            cov.control_cg.sample(control_enables, 1'b0);
          end
        end
      end
      "cfg_cdc_sync": begin
        // rw1c: When written to 1 this bit self-clears when the slow clock domain
        // syncs.
        do_read_check = 1'b0;
      end
      "wakeup_en_regwen": begin
      end
      "wakeup_en": begin
      end
      "wake_status": begin
        // Read-only.
        do_read_check = 1'b0;
      end
      "reset_en_regwen": begin
        // rw0c, so writing a 1 is a no-op.
      end
      "reset_en": begin
        if (data_phase_write) begin
          cfg.pwrmgr_vif.update_reset_en(item.a_data);
        end
      end
      "reset_status": begin
        // Read-only.
        do_read_check = 1'b0;
      end
      "escalate_reset_status": begin
        // Read-only.
        do_read_check = 1'b0;
      end
      "wake_info_capture_dis": begin
      end
      "wake_info": begin
        // rw1c: write 1 clears, write 0 is no-op.
        do_read_check = 1'b0;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      `uvm_info(`gfn, $sformatf("Reading 0x%x from %s", item.d_data, csr.get_full_name()), UVM_LOW)
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
