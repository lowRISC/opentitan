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
    super.build_phase(phase);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    cfg.run_phase = phase;
    fork
      wakeup_ctrl_coverage_collector();
      wakeup_intr_coverage_collector();
      low_power_coverage_collector();
    join_none
  endtask

  task wakeup_ctrl_coverage_collector();
    forever
      @(posedge cfg.pwrmgr_vif.wakeups_i) begin
        if (cfg.en_cov) begin
          foreach (cov.wakeup_ctrl_cg_wrap[i]) begin
            cov.wakeup_ctrl_cg_wrap[i].sample(
                cfg.pwrmgr_vif.wakeup_en[i], cfg.pwrmgr_vif.wakeup_capture_en,
                cfg.pwrmgr_vif.wakeups_i[i], cfg.pwrmgr_vif.wakeup_status[i]);
          end
        end
      end
  endtask

  task wakeup_intr_coverage_collector();
    forever
      @(posedge (cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateRomCheck)) begin
        if (cfg.en_cov) begin
          foreach (cov.wakeup_intr_cg_wrap[i]) begin
            cov.wakeup_intr_cg_wrap[i].sample(cfg.pwrmgr_vif.wakeup_status[i],
                                              cfg.pwrmgr_vif.intr_enable,
                                              cfg.pwrmgr_vif.intr_wakeup);
          end
        end
      end
  endtask

  task low_power_coverage_collector();
    forever
      @(posedge cfg.pwrmgr_vif.pwr_rst_req.reset_cause == pwrmgr_pkg::LowPwrEntry) begin
        if (cfg.en_cov) begin
          cov.clock_control_cg.sample(cfg.pwrmgr_vif.clk_enables.core_clk_en,
                                      cfg.pwrmgr_vif.clk_enables.io_clk_en,
                                      cfg.pwrmgr_vif.clk_enables.usb_clk_en_lp,
                                      cfg.pwrmgr_vif.clk_enables.usb_clk_en_active);
        end
      end
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

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      `uvm_info(`gfn, $sformatf("Writing 0x%x to %s", item.a_data, csr.get_full_name()), UVM_LOW)
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    // TODO handle more read checks.
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        // rw1c: write 1 clears, write 0 is no-op.
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
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
          bit core_clk_en = get_field_val(ral.control.core_clk_en, item.a_data);
          bit io_clk_en = get_field_val(ral.control.io_clk_en, item.a_data);
          bit usb_clk_en_lp = get_field_val(ral.control.usb_clk_en_lp, item.a_data);
          bit usb_clk_en_active = get_field_val(ral.control.usb_clk_en_active, item.a_data);
          bit main_pd_n = get_field_val(ral.control.main_pd_n, item.a_data);
          cfg.pwrmgr_vif.update_clock_enables(
              '{core_clk_en, io_clk_en, usb_clk_en_lp, usb_clk_en_active, main_pd_n});
        end
      end
      "cfg_cdc_sync": begin
        // rw1c: When written to 1 this bit self-clears when the slow clock domain
        // syncs.
        do_read_check = 1'b0;
      end
      "wakeup_en_regwen": begin
        // rw0c, so writing a 1 is a no-op.
        if (data_phase_write) begin
          cfg.pwrmgr_vif.update_wakeup_en_regwen(item.a_data);
        end
      end
      "wakeup_en": begin
        if (data_phase_write) begin
          cfg.pwrmgr_vif.update_wakeup_en(item.a_data);
        end
      end
      "wake_status": begin
        // Read-only.
        do_read_check = 1'b0;
      end
      "reset_en_regwen": begin
        // rw0c, so writing a 1 is a no-op.
      end
      "reset_en": begin
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
        if (data_phase_write) begin
          cfg.pwrmgr_vif.update_wakeup_capture_dis(item.a_data);
        end
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
