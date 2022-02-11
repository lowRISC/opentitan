// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cip_base_scoreboard #(type RAL_T = dv_base_reg_block,
                            type CFG_T = cip_base_env_cfg,
                            type COV_T = cip_base_env_cov)
                            extends dv_base_scoreboard #(RAL_T, CFG_T, COV_T);
  `uvm_component_param_utils(cip_base_scoreboard #(RAL_T, CFG_T, COV_T))

  // TLM fifos to pick up the packets
  uvm_tlm_analysis_fifo #(tl_channels_e) tl_dir_fifos[string];
  uvm_tlm_analysis_fifo #(tl_seq_item)   tl_a_chan_fifos[string];
  uvm_tlm_analysis_fifo #(tl_seq_item)   tl_d_chan_fifos[string];

  // Alert_fifo to notify scb if DUT sends an alert
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) alert_fifos[string];

  // EDN fifo
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(EDN_DATA_WIDTH))) edn_fifos[];

  mem_model#() exp_mem[string];

  // alert checking related parameters
  bit do_alert_check = 1;
  bit check_alert_sig_int_err = 1;
  local bit under_alert_handshake[string];
  local bit exp_alert[string];
  local bit is_fatal_alert[string];
  local int alert_chk_max_delay[string];
  local int alert_count[string];

  // intg check
  bit en_d_user_intg_chk = 1;

  // covergroups
  tl_errors_cg_wrap   tl_errors_cgs_wrap[string];
  tl_intg_err_cg_wrap tl_intg_err_cgs_wrap[string];
  tl_intg_err_mem_subword_cg_wrap tl_intg_err_mem_subword_cgs_wrap[string];
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    foreach (cfg.m_tl_agent_cfgs[i]) begin
      tl_a_chan_fifos[i] = new({"tl_a_chan_fifo_", i}, this);
      tl_d_chan_fifos[i] = new({"tl_d_chan_fifo_", i}, this);
      tl_dir_fifos[i] = new({"tl_dir_fifo_", i}, this);
    end
    foreach(cfg.list_of_alerts[i]) begin
      string alert_name = cfg.list_of_alerts[i];
      alert_fifos[alert_name] = new($sformatf("alert_fifo[%s]", alert_name), this);
    end
    edn_fifos = new[cfg.num_edn];
    foreach (cfg.m_edn_pull_agent_cfg[i]) edn_fifos[i] = new($sformatf("edn_fifos[%0d]", i), this);
    foreach (cfg.m_tl_agent_cfgs[i]) begin
      exp_mem[i] = mem_model#()::type_id::create({"exp_mem_", i}, this);
    end

    foreach (cfg.ral_models[ral_name]) begin
      bit has_unmapped  = (cfg.ral_models[ral_name].unmapped_addr_ranges.size > 0);
      bit has_csr       = (cfg.ral_models[ral_name].csr_addrs.size > 0);
      bit has_mem       = (cfg.ral_models[ral_name].mem_ranges.size > 0);
      bit has_mem_byte_access_err;
      bit has_wo_mem;
      bit has_ro_mem;

      if (has_mem) begin
        get_all_mem_attrs(cfg.ral_models[ral_name], has_mem_byte_access_err, has_wo_mem, has_ro_mem);
      end

      tl_errors_cgs_wrap[ral_name] = new($sformatf("tl_errors_cgs_wrap[%0s]", ral_name));
      if (!has_csr) begin
        tl_errors_cgs_wrap[ral_name].tl_errors_cg.cp_csr_size_err.option.weight = 0;
      end
      if (!has_unmapped) begin
        tl_errors_cgs_wrap[ral_name].tl_errors_cg.cp_unmapped_err.option.weight = 0;
      end
      if (!has_mem_byte_access_err) begin
        tl_errors_cgs_wrap[ral_name].tl_errors_cg.cp_mem_byte_access_err.option.weight = 0;
      end
      if (!has_wo_mem) begin
        tl_errors_cgs_wrap[ral_name].tl_errors_cg.cp_mem_wo_err.option.weight = 0;
      end
      if (!has_ro_mem) begin
        tl_errors_cgs_wrap[ral_name].tl_errors_cg.cp_mem_ro_err.option.weight = 0;
      end

      if (has_mem) begin
        tl_intg_err_mem_subword_cgs_wrap[ral_name] = new(
            $sformatf("tl_intg_err_mem_subword_cgs_wrap[%0s]", ral_name));
      end

      tl_intg_err_cgs_wrap[ral_name] = new($sformatf("tl_intg_err_cgs_wrap[%0s]", ral_name));
      if (!has_mem || !has_csr) begin
        tl_intg_err_cgs_wrap[ral_name].tl_intg_err_cg.cp_is_mem.option.weight = 0;
      end
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_tl_fifos();
      if (cfg.list_of_alerts.size()) process_alert_fifos();
      if (cfg.list_of_alerts.size()) check_alerts();
    join_none
  endtask

  task process_tl_fifos();
    foreach (cfg.m_tl_agent_cfgs[i]) begin
      automatic string ral_name = i;
      process_tl_fifo(i, tl_dir_fifos[i], tl_a_chan_fifos[i], tl_d_chan_fifos[i]);
    end
  endtask

  task process_tl_fifo(string ral_name,
                       uvm_tlm_analysis_fifo #(tl_channels_e) dir_fifo,
                       uvm_tlm_analysis_fifo #(tl_seq_item) a_chan_fifo,
                       uvm_tlm_analysis_fifo #(tl_seq_item) d_chan_fifo);
    tl_channels_e dir;
    tl_seq_item   item;

    fork
      forever begin
        dir_fifo.get(dir);
        case (dir)
          AddrChannel: begin
            `DV_CHECK_FATAL(a_chan_fifo.try_get(item),
                            "dir_fifo pointed at A channel, but a_chan_fifo empty")
            process_tl_a_item(ral_name, item);
          end

          DataChannel: begin
            `DV_CHECK_FATAL(d_chan_fifo.try_get(item),
                            "dir_fifo pointed at D channel, but d_chan_fifo empty")
            process_tl_d_item(ral_name, item);
          end

          default: `uvm_fatal(`gfn, "Invalid entry in dir_fifo")
        endcase
      end
    join_none
  endtask

  task process_tl_a_item(string ral_name, tl_seq_item item);
    `uvm_info(`gfn, $sformatf("received tl a_chan item: %0s", item.convert2string()), UVM_HIGH)

    if (cfg.en_scb_tl_err_chk) begin
      if (predict_tl_err(item, AddrChannel, ral_name)) return;
    end
    if (!cfg.en_scb) return;

    process_tl_access(item, AddrChannel, ral_name);
  endtask

  task process_tl_d_item(string ral_name, tl_seq_item item);
    `uvm_info(`gfn, $sformatf("received tl d_chan item: %0s", item.convert2string()), UVM_HIGH)

    if (cfg.en_scb_tl_err_chk) begin
      // check tl packet integrity
      void'(item.is_ok());
      if (predict_tl_err(item, DataChannel, ral_name)) return;
    end
    if (cfg.en_scb_mem_chk && is_mem_addr(item, ral_name)) begin
      if (item.is_write()) begin
        process_mem_write(item, ral_name);
      end else begin
        process_mem_read(item, ral_name);
      end
    end

    if (!cfg.en_scb) return;

    process_tl_access(item, DataChannel, ral_name);
  endtask

  virtual task process_alert_fifos();
    foreach (alert_fifos[i]) begin
      automatic string alert_name = i;
      fork
        forever begin
          alert_esc_seq_item item;
          alert_fifos[alert_name].get(item);
          if (!cfg.en_scb) continue;
          if (item.alert_esc_type == AlertEscSigTrans && !item.ping_timeout &&
              item.alert_handshake_sta inside {AlertReceived, AlertAckComplete}) begin
            process_alert(alert_name, item);
          // IP level alert protocol does not drive any sig_int_err or ping response.
          // However, `lpg_en` or `alert_init` will trigger signal integrity error, user can
          // disable signal integrity checking via `check_alert_sig_int_err` flag.
          end else if (check_alert_sig_int_err && item.alert_esc_type == AlertEscIntFail) begin
            `uvm_error(`gfn, $sformatf("alert %s has unexpected signal int error", alert_name))
          end else if (item.ping_timeout) begin
            `uvm_error(`gfn, $sformatf("alert %s has unexpected timeout error", alert_name))
          end else if (item.alert_esc_type == AlertEscPingTrans) begin
            `uvm_error(`gfn, $sformatf("alert %s has unexpected alert ping response", alert_name))
          end
        end
      join_none
    end
  endtask

  // Called at the start of each alert handshake. The default implementation depends on the
  // do_alert_check flag. If that is set, it checks that an alert is expected (by checking
  // exp_alert[alert_name]).
  virtual function void on_alert(string alert_name, alert_esc_seq_item item);
    if (do_alert_check) begin
      `DV_CHECK_EQ(exp_alert[alert_name], 1,
                   $sformatf("alert %0s triggered unexpectedly", alert_name))
    end
  endfunction

  // this function check if the triggered alert is expected
  // to turn off this check, user can set `do_alert_check` to 0
  virtual function void process_alert(string alert_name, alert_esc_seq_item item);
    if (!(alert_name inside {cfg.list_of_alerts})) begin
      `uvm_fatal(`gfn, $sformatf("alert_name %0s is not in cfg.list_of_alerts!", alert_name))
    end

    `uvm_info(`gfn, $sformatf("alert %0s detected, alert_status is %s", alert_name,
                              item.alert_handshake_sta), UVM_DEBUG)
    if (item.alert_handshake_sta == AlertReceived) begin
      under_alert_handshake[alert_name] = 1;
      on_alert(alert_name, item);
      ++alert_count[alert_name];
    end else begin
      if (!cfg.under_reset && under_alert_handshake[alert_name] == 0) begin
        `uvm_error(`gfn, $sformatf("alert %0s is not received!", alert_name))
      end
      under_alert_handshake[alert_name] = 0;
    end
  endfunction

  virtual function int get_alert_count(string alert_name);
    return alert_count[alert_name];
  endfunction

  // this task is implemented to check if expected alert is triggered within certain clock cycles
  // if alert is fatal alert, it will expect alert handshakes until reset
  // if alert is not fatal alert, it will set exp_alert back to 0 once finish alert_checking
  virtual task check_alerts();
    foreach (cfg.list_of_alerts[i]) begin
      automatic string alert_name = cfg.list_of_alerts[i];
      fork
        forever begin
          wait(exp_alert[alert_name] == 1 && cfg.under_reset == 0);
          if (is_fatal_alert[alert_name]) begin
            while (cfg.under_reset == 0) begin
              check_alert_triggered(alert_name);
              wait(under_alert_handshake[alert_name] == 0 || cfg.under_reset == 1);
            end
          end else begin
            check_alert_triggered(alert_name);
            exp_alert[alert_name] = 0;
          end
        end
      join_none
    end
  endtask

  virtual task check_alert_triggered(string alert_name);
    // Add 1 extra negedge edge clock to make sure no race condition.
    repeat(alert_esc_agent_pkg::ALERT_B2B_DELAY + 1 + alert_chk_max_delay[alert_name]) begin
      cfg.clk_rst_vif.wait_n_clks(1);
      if (under_alert_handshake[alert_name] || cfg.under_reset) return;
    end
    `uvm_error(`gfn, $sformatf("alert %0s did not trigger", alert_name))
  endtask

  // This function is used for individual IPs to set when they expect certain alert to trigger
  // - Input alert_name is the full name of the alert listed in LIST_OF_ALERTS.
  // - Input is_fatal, if set, expects to continuously trigger alert request until reset is
  //   asserted.
  // - Input max_delay can be used when user could not predict the exact time when alert triggered.
  //   This input allows alert to trigger anytime between 0 to `max_delay` clock cycles. However,
  //   please do not use this variable if there is any ongoing alert handshake, because if using
  //   max_delay, we cannot accurately predict if two alerts are merged or not.
  virtual function void set_exp_alert(string alert_name, bit is_fatal = 0, int max_delay = 0);
    if (!(alert_name inside {cfg.list_of_alerts})) begin
      `uvm_fatal(`gfn, $sformatf("alert_name %0s is not in cfg.list_of_alerts!", alert_name))
    end
    fork
      begin
        // delay a negedge clk to avoid race condition between this function and
        // `under_alert_handshake` variable
        cfg.clk_rst_vif.wait_n_clks(1);
        if (under_alert_handshake[alert_name] || exp_alert[alert_name]) begin
          `uvm_info(`gfn, $sformatf("Current %0s alert status under_alert_handshake=%0b,\
                    exp_alert=%0b, request ignored", alert_name, under_alert_handshake[alert_name],
                    exp_alert[alert_name]), UVM_MEDIUM)
        end else begin
          `uvm_info(`gfn, $sformatf("alert %0s is expected to trigger", alert_name), UVM_MEDIUM)
          is_fatal_alert[alert_name] = is_fatal;
          exp_alert[alert_name] = 1;
          alert_chk_max_delay[alert_name] = max_delay;
        end
      end
    join_none
  endfunction

  // task to process tl access
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    `uvm_fatal(`gfn, "this method is not supposed to be called directly!")
  endtask

  virtual task process_mem_write(tl_seq_item item, string ral_name);
    uvm_reg_addr_t addr = cfg.ral_models[ral_name].get_normalized_addr(item.a_addr);
    if (!cfg.under_reset)  exp_mem[ral_name].write(addr, item.a_data, item.a_mask);
  endtask

  virtual task process_mem_read(tl_seq_item item, string ral_name);
    uvm_reg_addr_t addr = cfg.ral_models[ral_name].get_normalized_addr(item.a_addr);
    if (!cfg.under_reset && get_mem_access_by_addr(cfg.ral_models[ral_name], addr) == "RW") begin
      exp_mem[ral_name].compare(addr, item.d_data, item.a_mask);
    end
  endtask

  // check if it's mem addr
  virtual function bit is_mem_addr(tl_seq_item item, string ral_name);
    uvm_reg_addr_t addr = cfg.ral_models[ral_name].get_normalized_addr(item.a_addr);
    addr_range_t   loc_mem_ranges[$] = cfg.ral_models[ral_name].mem_ranges;
    foreach (loc_mem_ranges[i]) begin
      if (addr inside {[loc_mem_ranges[i].start_addr : loc_mem_ranges[i].end_addr]}) begin
        return 1;
      end
    end
    return 0;
  endfunction

  // Check if there is any tl error.
  //
  // On the Addr channel, returns 1 if the item should cause a TL error.
  //
  // On the Data channel, this also asserts that the item's D channel integrity is correct (because
  // the DUT should never inject errors) and that item.d_error matches the prediction (to check that
  // the DUT correctly spots TL errors on the A channel). If TL integrity generation is enabled,
  // this also calls update_tl_alert_field_prediction() to update the mirrored value of any "I've
  // seen an integrity error" bit.
  //
  // The following situations might cause a TL error:
  //
  //  - unmapped address
  //  - write address isn't word-aligned
  //  - memory write isn't a full word
  //  - register write size is less than actual register width
  //  - TL protocol violation
  virtual function bit predict_tl_err(tl_seq_item item, tl_channels_e channel, string ral_name);
    bit is_tl_unmapped_addr, is_tl_err, mem_access_err;
    bit csr_size_err, tl_item_err;
    bit has_intg_err;
    bit mem_byte_access_err, mem_wo_err, mem_ro_err;
    bit is_passthru_mem = is_data_intg_passthru_mem(item, ral_name);

    if (!is_tl_access_mapped_addr(item, ral_name)) begin
      is_tl_unmapped_addr = 1;
      // if devmode is enabled, d_error will be set
      if (cfg.en_devmode || cfg.devmode_vif.sample()) begin
        is_tl_err = 1;
      end
    end

    mem_access_err  = !is_tl_mem_access_allowed(item, ral_name, mem_byte_access_err, mem_wo_err,
                                                mem_ro_err);
    csr_size_err    = !is_tl_csr_write_size_gte_csr_width(item, ral_name);
    tl_item_err     = item.get_exp_d_error();

    has_intg_err = !item.is_a_chan_intg_ok(.throw_error(0));

    // If we got an error response caused by an integrity failure, update the mirrored value for
    // any bus integrity alert field (if there is one).
    if (has_intg_err) begin
      update_tl_alert_field_prediction();
    end

    if (channel == DataChannel) begin
      cip_tl_seq_item cip_item;
      tl_intg_err_e tl_intg_err_type;
      uint num_cmd_err_bits, num_data_err_bits;

      // integrity at d_user is from DUT, which should be always correct, except data integrity for
      // passthru memory
      void'(item.is_d_chan_intg_ok(
            .en_data_intg_chk(!is_passthru_mem ||
                              !cfg.disable_d_user_data_intg_check_for_passthru_mem),
            .throw_error(1)));

      // sample covergroup
      `downcast(cip_item, item)
      cip_item.get_a_chan_err_info(tl_intg_err_type, num_cmd_err_bits, num_data_err_bits);
      tl_intg_err_cgs_wrap[ral_name].sample(tl_intg_err_type, num_cmd_err_bits, num_data_err_bits,
                                            is_mem_addr(item, ral_name));

      if (tl_intg_err_mem_subword_cgs_wrap.exists(ral_name)) begin
        tl_intg_err_mem_subword_cgs_wrap[ral_name].sample(
            .tl_intg_err_type(tl_intg_err_type),
            .write(item.a_opcode != tlul_pkg::Get),
            .num_enable_bytes($countones(item.a_mask)));
      end
    end

    if (!is_tl_err && (mem_access_err || csr_size_err || tl_item_err ||
                       has_intg_err)) begin
      is_tl_err = 1;
    end
    if (channel == DataChannel) begin
      `DV_CHECK_EQ(item.d_error, is_tl_err,
          $sformatf({"On interface %0s, TL item: %0s, unmapped: %0d, mem_access_err: %0d, ",
                    "csr_size_err: %0d, tl_item_err: %0d, has_intg_err: %0d"}, ral_name,
                    item.sprint(uvm_default_line_printer), is_tl_unmapped_addr, mem_access_err,
                    csr_size_err, tl_item_err, has_intg_err))

      // TODO: check d_data to be all ones when memory related error occurs.

      // these errors all have the same outcome. Only sample coverages when there is just one
      // error, so that we know the error actually triggers the outcome
      if (is_tl_unmapped_addr + csr_size_err + mem_byte_access_err + mem_wo_err +
          mem_ro_err + tl_item_err == 1) begin
        tl_errors_cgs_wrap[ral_name].sample(.unmapped_err(is_tl_unmapped_addr),
                                            .csr_size_err(csr_size_err),
                                            .mem_byte_access_err(mem_byte_access_err),
                                            .mem_wo_err(mem_wo_err),
                                            .mem_ro_err(mem_ro_err),
                                            .tl_protocol_err(tl_item_err));
      end

    end
    return (is_tl_unmapped_addr || is_tl_err);
  endfunction

  // check if address is mapped
  virtual function bit is_tl_access_mapped_addr(tl_seq_item item, string ral_name);
    uvm_reg_addr_t addr = cfg.ral_models[ral_name].get_normalized_addr(item.a_addr);
    // check if it's mem addr or reg addr
    return is_mem_addr(item, ral_name) || addr inside {cfg.ral_models[ral_name].csr_addrs};
  endfunction

  // check if tl mem access will trigger error or not
  virtual function bit is_tl_mem_access_allowed(input tl_seq_item item, input string ral_name,
                                                output bit mem_byte_access_err,
                                                output bit mem_wo_err,
                                                output bit mem_ro_err);
    if (is_mem_addr(item, ral_name)) begin
      bit mem_partial_write_support;
      dv_base_mem mem;
      uvm_reg_addr_t addr = cfg.ral_models[ral_name].get_normalized_addr(item.a_addr);
      string mem_access = get_mem_access_by_addr(cfg.ral_models[ral_name], addr);

      `downcast(mem, get_mem_by_addr(cfg.ral_models[ral_name], addr))
      mem_partial_write_support = mem.get_mem_partial_write_support();

      // check if write isn't full word for mem that doesn't allow byte access
      if (!mem_partial_write_support && (item.a_size != 2 || item.a_mask != '1) &&
           item.a_opcode inside {tlul_pkg::PutFullData, tlul_pkg::PutPartialData}) begin
        mem_byte_access_err = 1;
      end

      // check if mem read happens while mem doesn't allow read (WO)
      mem_wo_err = (mem_access == "WO") && (item.a_opcode == tlul_pkg::Get);

      // check if mem write happens while mem is RO
      mem_ro_err = (mem_access == "RO") && (item.a_opcode != tlul_pkg::Get);

      if (mem_byte_access_err || mem_wo_err || mem_ro_err) begin
        `uvm_info(`gfn, $sformatf("mem_byte_access_err = %0d, mem_wo_err = %0d, mem_ro_err = %0d",
                                  mem_byte_access_err, mem_wo_err, mem_ro_err), UVM_HIGH)
        return 0;
      end
    end
    return 1;
  endfunction

  virtual function bit is_data_intg_passthru_mem(tl_seq_item item, string ral_name);
    uvm_reg_addr_t addr = cfg.ral_models[ral_name].get_normalized_addr(item.a_addr);
    uvm_mem mem = cfg.ral_models[ral_name].default_map.get_mem_by_offset(addr);

    if (mem == null) begin
      return 0;
    end else begin
      dv_base_mem dv_mem;
      `downcast(dv_mem, mem)
      return dv_mem.get_data_intg_passthru();
    end
  endfunction

  // check if csr write size greater or equal to csr width
  virtual function bit is_tl_csr_write_size_gte_csr_width(tl_seq_item item, string ral_name);
    if (!is_tl_access_mapped_addr(item, ral_name) || is_mem_addr(item, ral_name)) return 1;
    if (item.is_write()) begin
      dv_base_reg    csr;
      uvm_reg_addr_t addr = cfg.ral_models[ral_name].get_normalized_addr(item.a_addr);
      `DV_CHECK_FATAL($cast(csr,
                            cfg.ral_models[ral_name].default_map.get_reg_by_offset(addr)))
      if (csr.get_msb_pos >= 24 && item.a_mask[3:0] != 'b1111 ||
          csr.get_msb_pos >= 16 && item.a_mask[2:0] != 'b111  ||
          csr.get_msb_pos >= 8  && item.a_mask[1:0] != 'b11   ||
          item.a_mask[0] != 'b1) begin
        return 0;
      end
    end
    return 1;
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    foreach (tl_a_chan_fifos[i]) tl_a_chan_fifos[i].flush();
    foreach (tl_d_chan_fifos[i]) tl_d_chan_fifos[i].flush();
    foreach (edn_fifos[i]) edn_fifos[i].flush();
    foreach(cfg.list_of_alerts[i]) begin
      alert_fifos[cfg.list_of_alerts[i]].flush();
      exp_alert[cfg.list_of_alerts[i]]             = 0;
      under_alert_handshake[cfg.list_of_alerts[i]] = 0;
      is_fatal_alert[cfg.list_of_alerts[i]]        = 0;
      alert_chk_max_delay[cfg.list_of_alerts[i]]   = 0;
    end
  endfunction

  virtual task sample_resets();
    if (cfg.num_edn && cfg.en_cov) begin
      // Discard the first resets
      wait(cfg.clk_rst_vif.rst_n && cfg.edn_clk_rst_vif.rst_n);
      forever begin
        @(cfg.clk_rst_vif.rst_n or cfg.edn_clk_rst_vif.rst_n);
        cov.resets_cg.sample({cfg.clk_rst_vif.rst_n, cfg.edn_clk_rst_vif.rst_n});
      end
    end
  endtask

  virtual function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    foreach (tl_a_chan_fifos[i]) `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, tl_a_chan_fifos[i])
    foreach (tl_d_chan_fifos[i]) `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, tl_d_chan_fifos[i])
  endfunction

  virtual function void update_tl_alert_field_prediction();
    foreach (cfg.tl_intg_alert_fields[field]) begin
      uvm_reg_data_t value = cfg.tl_intg_alert_fields[field];
      `DV_CHECK_FATAL(field, "field is Null in tl_intg_alert_fields")

      // Set the field
      `DV_CHECK_FATAL(field.predict(.value(value), .kind(UVM_PREDICT_READ)));
    end
  endfunction

endclass
