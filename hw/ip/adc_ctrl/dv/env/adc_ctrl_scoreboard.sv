// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_scoreboard extends cip_base_scoreboard #(
  .CFG_T(adc_ctrl_env_cfg),
  .RAL_T(adc_ctrl_reg_block),
  .COV_T(adc_ctrl_env_cov)
);


  // Analysis FIFOs for ADC push pull monitor transactions
  adc_push_pull_fifo_t m_adc_push_pull_fifo[ADC_CTRL_CHANNELS];

  // Latest value for each channel
  protected adc_value_logic_t m_adc_latest_values[int] = '{default: 0};

  // Interrupt value for each channel
  protected adc_value_logic_t m_adc_interrupt_values[int] = '{default: 0};

  // Interrupt line
  protected logic m_interrupt;
  // Wakeup line
  protected logic m_wakeup;

  // ADC Model variables
  // Filter match for each filter of each channel
  protected bit [ADC_CTRL_CHANNELS - 1 : 0][ADC_CTRL_NUM_FILTERS-1 : 0] m_chn_match;
  // Combined matches from all channels
  protected bit [ADC_CTRL_NUM_FILTERS-1 : 0] m_match, m_match_prev;
  // Normal power and low power sample match counters
  protected uint16_t m_np_counter, m_lp_counter;
  // Expected filter status bits
  protected bit [ADC_CTRL_NUM_FILTERS - 1 : 0] m_expected_filter_status;
  // Debounce detected
  protected bit m_debounced;
  // Expected adc_intr_status (1 bit per filter + oneshot mode)
  protected bit [ADC_CTRL_NUM_FILTERS : 0] m_expected_adc_intr_status;
  // Expected intr_state register
  protected bit m_expected_intr_state;
  // Write to filter_status
  protected event m_filter_status_wr_ev;
  // Write to adc_intr_status
  protected event m_adc_intr_status_wr_ev;
  // Write to intr_state
  protected event m_intr_state_wr_ev;
  // Expected wakeup line
  protected bit m_expected_wakeup;
  // Write to adc_fsm_reset
  protected event m_adc_fsm_reset_wr_ev;
  // FSM reset reg value
  protected bit m_adc_fsm_reset;
  // ADC_CTRL enabled
  protected bit m_adc_ctrl_en = 0;
  // In low power mode
  protected bit m_lp_mode = 0;
  // Debug cable index in interupt registers
  protected int unsigned m_debug_cable_index;

  `uvm_component_utils(adc_ctrl_scoreboard)

  // local variables

  // TLM agent fifos

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Create ADC push pull FIFOs
    for (int idx = 0; idx < ADC_CTRL_CHANNELS; idx++) begin
      string name = $sformatf("m_adc_push_pull_fifo_%0d", idx);
      m_adc_push_pull_fifo[idx] = new(name, this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    m_debug_cable_index = cfg.ral.intr_state.debug_cable.get_lsb_pos();
  endfunction

  task run_phase(uvm_phase phase);
    int idx = 0;
    super.run_phase(phase);
    fork
      monitor_intr_proc();
      monitor_wakeup_proc();
      monitor_aon_reset_proc();
    join_none

    for (idx = 0; idx < ADC_CTRL_CHANNELS; idx++) begin
      // Local copy see LRM 9.3.2 for details
      int idx_local = idx;
      fork
        adc_push_pull_fifo_proc(m_adc_push_pull_fifo[idx_local], idx_local);
      join_none
    end
  endtask


  // Monitor interrupt line
  protected virtual task monitor_intr_proc();
    bit intr_en;
    forever begin
      @(cfg.intr_vif.pins);
      m_interrupt = cfg.intr_vif.sample_pin(ADC_CTRL_INTERRUPT_INDEX);
      // Compare against expected every change of interrupt line
      if (cfg.en_scb) begin
        intr_en = ral.intr_enable.debug_cable.get_mirrored_value();
        `uvm_info(`gfn, $sformatf(
                  "monitor_intr_proc: interrupt pin change m_interrupt=%b", m_interrupt),
                  UVM_MEDIUM)
        `DV_CHECK_EQ(m_interrupt, (m_expected_intr_state & intr_en))
        if (cfg.en_cov) begin
          // Sample interrupt pin coverage for interrupt pins
          cov.intr_pins_cg.sample(ADC_CTRL_INTERRUPT_INDEX, m_interrupt);
          // Sample filter interrupt clk_gate
          if (m_interrupt)
            sample_filter_cov(.is_interrupt(1), .is_wakeup(0), .clk_gate(cfg.clk_rst_vif.clk_gate));
        end
      end
    end
  endtask

  // Monitor wakeup line
  protected virtual task monitor_wakeup_proc();
    forever begin
      @(cfg.wakeup_vif.pins);
      m_wakeup = cfg.wakeup_vif.sample_pin(0);
      if (cfg.en_scb) begin
        `uvm_info(`gfn, $sformatf("monitor_wakeup_proc: wakeup pin change m_wakeup=%b", m_wakeup),
                  UVM_MEDIUM)
        `DV_CHECK_EQ(m_wakeup, m_expected_wakeup)

        if (cfg.en_cov) begin
          // Sample filter wakeup clk_gate
          if (m_wakeup)
            sample_filter_cov(.is_interrupt(0), .is_wakeup(1), .clk_gate(cfg.clk_rst_vif.clk_gate));
        end
      end
    end
  endtask

  // Monitor always on clock reset
  virtual task monitor_aon_reset_proc();
    forever begin
      if (!cfg.clk_aon_rst_vif.rst_n) begin
        `uvm_info(`gfn, "aon reset occurred", UVM_HIGH)
        reset("HARD");
        m_expected_wakeup = 0;
        @(posedge cfg.clk_aon_rst_vif.rst_n);
        `uvm_info(`gfn, "out of reset", UVM_HIGH)
      end else begin
        // wait for a change to rst_n
        @(cfg.clk_aon_rst_vif.rst_n);
      end
    end
  endtask

  // Process ADC push pull fifos
  protected virtual task adc_push_pull_fifo_proc(adc_push_pull_fifo_t fifo, int channel);
    adc_push_pull_item_t item;
    forever begin
      fifo.get(item);
      cfg.trigger_adc_rx_event(channel);
      // Set latest value
      m_adc_latest_values[channel] = item.d_data;

      // Send data to filter model if ADC_CTRL enabled
      if (m_adc_ctrl_en) process_filter_data(channel, item.d_data);

      `uvm_info(
          `gfn, $sformatf(
          "adc_push_pull_fifo_proc channel %0d: %s", channel, item.sprint(uvm_default_line_printer)
          ), UVM_MEDIUM)
    end
  endtask

  // Return the latest ADC value for the respective channel
  virtual function adc_value_logic_t get_adc_latest_value(input int channel);
    adc_value_logic_t value = m_adc_latest_values[channel];
    `uvm_info(`gfn, $sformatf("get_adc_latest_value channel=%0d  value=%0h", channel, value),
              UVM_HIGH)
    return value;
  endfunction

  // Return the latest ADC interrupt value for the respective channel
  virtual function adc_value_logic_t get_adc_interrupt_value(input int channel);
    adc_value_logic_t value = m_adc_interrupt_values[channel];
    `uvm_info(`gfn, $sformatf("get_adc_interrupt_value channel=%0d  value=%0h", channel, value),
              UVM_HIGH)
    return value;
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    bit            do_read_check = 1'b1;
    bit            write = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit            addr_phase_read = (!write && channel == AddrChannel);
    bit            addr_phase_write = (write && channel == AddrChannel);
    bit            data_phase_read = (!write && channel == DataChannel);
    bit            data_phase_write = (write && channel == DataChannel);
    uvm_reg_data_t write_data;

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        bit intr_en = ral.intr_enable.debug_cable.get_mirrored_value();
        do_read_check = 1;
        if (addr_phase_write) begin
          ->m_intr_state_wr_ev;
          // Implement W1C
          m_expected_intr_state &= !get_field_val(cfg.ral.intr_state.debug_cable, item.a_data);
        end
        if (addr_phase_read) begin
          `DV_CHECK(csr.predict(.value(m_expected_intr_state), .kind(UVM_PREDICT_READ)))
        end
        if (cfg.en_cov && data_phase_read) begin
          cov.intr_cg.sample(m_debug_cable_index, intr_en, get_field_val(
                             cfg.ral.intr_state.debug_cable, item.a_data));
        end
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
        // Model intr_test functionality
        bit intr_test_val = get_field_val(cfg.ral.intr_test.debug_cable, item.a_data);
        bit intr_en = ral.intr_enable.debug_cable.get_mirrored_value();
        if (addr_phase_write) begin
          m_expected_intr_state |= intr_test_val;
          if (cfg.en_cov) begin
            cov.intr_test_cg.sample(m_debug_cable_index, intr_test_val, intr_en,
                                    m_expected_intr_state);
          end
        end
      end
      "adc_intr_status": begin
        // TODO: update modeling for One Shot mode
        do_read_check = 1;
        if (addr_phase_write) begin
          ->m_adc_intr_status_wr_ev;
          // Implement W1C
          m_expected_adc_intr_status &= (~item.a_data);
        end
        if (addr_phase_read) begin
          `DV_CHECK(csr.predict(.value(m_expected_adc_intr_status), .kind(UVM_PREDICT_READ)))
        end
      end
      "adc_intr_ctl": begin
        // FIXME
      end
      "adc_wakeup_ctl": begin
        if (addr_phase_write) begin
          // Evaluate expected wakeup adc_wakeup_ctl
          m_expected_wakeup =
              |(m_expected_filter_status & get_field_val(cfg.ral.adc_wakeup_ctl.en, item.a_data));
        end
      end
      "adc_en_ctl": begin
        if (addr_phase_write) begin
          m_adc_ctrl_en = get_field_val(cfg.ral.adc_en_ctl.adc_enable, item.a_data);
          if (m_adc_ctrl_en) begin
            // Enable the ADC_CTRL
            // Update mode from adc_pd_ctl but only if not oneshot mode
            if (!get_field_val(cfg.ral.adc_en_ctl.oneshot_mode, item.a_data)) begin
              m_lp_mode = cfg.ral.adc_pd_ctl.lp_mode.get_mirrored_value();
            end else begin
              // Oneshot mode
              m_lp_mode = 0;
            end

            // Update filter match using previously captured data
            foreach (m_adc_latest_values[channel]) begin
              process_filter_data(.channel(channel), .val(m_adc_latest_values[channel]),
                                  .call_debounce(0));
            end
            m_match_prev = 0;

            // Sample configuration_coverage
            if (cfg.en_cov) begin
              sample_filter_cov(.is_interrupt(0), .is_wakeup(0));
              sample_testmode_cov();
            end

          end else begin
            // Disable the ADC_CTRL
            m_lp_counter = 0;
            m_np_counter = 0;
            m_debounced = 0;
            m_lp_mode = 0;
          end
          // Reflect in config object
          cfg.lp_mode = m_lp_mode;
        end
      end
      "filter_status": begin
        do_read_check = 1;
        if (addr_phase_read) begin
          // Latest ADC value
          void'(ral.filter_status.predict(
              .value(m_expected_filter_status), .kind(UVM_PREDICT_READ)
          ));
        end
        if (addr_phase_write) begin
          ->m_filter_status_wr_ev;
          // Implement W1C
          m_expected_filter_status &= (~item.a_data);
        end
        // Evaluate expected wakeup for new m_expected_filter_status
        m_expected_wakeup = |(m_expected_filter_status &
            cfg.ral.adc_wakeup_ctl.get_mirrored_value());
      end
      "adc_chn0_filter_ctl_0", "adc_chn0_filter_ctl_1", "adc_chn0_filter_ctl_2",
          "adc_chn0_filter_ctl_3", "adc_chn0_filter_ctl_4", "adc_chn0_filter_ctl_5",
          "adc_chn0_filter_ctl_6", "adc_chn0_filter_ctl_7", "adc_chn1_filter_ctl_0",
          "adc_chn1_filter_ctl_1", "adc_chn1_filter_ctl_2", "adc_chn1_filter_ctl_3",
          "adc_chn1_filter_ctl_4", "adc_chn1_filter_ctl_5", "adc_chn1_filter_ctl_6",
          "adc_chn1_filter_ctl_7"
          : begin
        // FIXME
      end

      "adc_chn_val_0": begin
        // Predict values
        if (addr_phase_read) begin
          // Latest ADC value
          void'(ral.adc_chn_val[0].adc_chn_value.predict(
              .value(get_adc_latest_value(0)), .kind(UVM_PREDICT_READ)
          ));

          // Interrupt ADC value
          `uvm_info(`gfn, $sformatf(
                    "adc_en_ctl.oneshot_mode=%0x", ral.adc_en_ctl.oneshot_mode.get_mirrored_value()
                    ), UVM_HIGH)
          if (ral.adc_en_ctl.oneshot_mode.get_mirrored_value() == 1) begin
            // In oneshot mode latest and interrupt fields are the same
            void'(ral.adc_chn_val[0].adc_chn_value_intr.predict(
                .value(get_adc_latest_value(0)), .kind(UVM_PREDICT_READ)
            ));
          end else begin
            // Interrupt value
            void'(ral.adc_chn_val[0].adc_chn_value_intr.predict(
                .value(get_adc_interrupt_value(0)), .kind(UVM_PREDICT_READ)
            ));
          end
        end
      end
      "adc_chn_val_1": begin
        // Predict values
        if (addr_phase_read) begin

          void'(ral.adc_chn_val[1].adc_chn_value.predict(
              .value(get_adc_latest_value(1)), .kind(UVM_PREDICT_READ)
          ));

          // Interrupt ADC value
          if (ral.adc_en_ctl.oneshot_mode.get_mirrored_value() == 1) begin
            // In oneshot mode latest and interrupt fields are the same
            void'(ral.adc_chn_val[1].adc_chn_value_intr.predict(
                .value(get_adc_latest_value(1)), .kind(UVM_PREDICT_READ)
            ));
          end else begin
            // Interrupt value
            void'(ral.adc_chn_val[1].adc_chn_value_intr.predict(
                .value(get_adc_interrupt_value(1)), .kind(UVM_PREDICT_READ)
            ));
          end
        end
      end

      // FSM Reset
      "adc_fsm_rst": begin
        if (addr_phase_write) begin
          ->m_adc_fsm_reset_wr_ev;
          do_adc_fsm_reset(item.a_data[0]);
        end
      end

      default: begin
        //`uvm_error(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check && cfg.en_scb) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, $sformatf(
                     "reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  // Sample the filter coverage using values from the register model
  // Set is_interrupt to notify an interrupt and is_wakeup a wakeup event
  virtual function void sample_filter_cov(bit is_interrupt = 0, bit is_wakeup = 0,
                                          bit clk_gate = 0);
    for (int channel = 0; channel < ADC_CTRL_CHANNELS; channel++) begin
      for (int filter = 0; filter < ADC_CTRL_NUM_FILTERS; filter++) begin
        string reg_name = $sformatf("adc_chn%0d_filter_ctl_%0d", channel, filter);
        adc_ctrl_filter_cfg_t cfg;
        cfg.en = get_reg_fld_mirror_value(ral, reg_name, "en");
        cfg.cond = adc_ctrl_filter_cond_e'(get_reg_fld_mirror_value(ral, reg_name, "cond"));
        cfg.min_v = get_reg_fld_mirror_value(ral, reg_name, "min_v");
        cfg.max_v = get_reg_fld_mirror_value(ral, reg_name, "max_v");
        cov.sample_filter_cov(.channel(channel), .filter(filter), .cfg(cfg),
                              .is_interrupt(is_interrupt), .is_wakeup(is_wakeup),
                              .clk_gate(clk_gate));
      end
    end
  endfunction

  // Decode and sample testmode from the register model
  virtual function void sample_testmode_cov();
    bit oneshot_mode = get_reg_fld_mirror_value(ral, "adc_en_ctl", "oneshot_mode");
    bit lp_mode = get_reg_fld_mirror_value(ral, "adc_pd_ctl", "lp_mode");
    adc_ctrl_testmode_e testmode;

    // Decode test modes
    unique case ({
      oneshot_mode, lp_mode
    })
      2'b00: testmode = AdcCtrlTestmodeNormal;
      2'b01: testmode = AdcCtrlTestmodeLowpower;
      2'b10, 2'b11: testmode = AdcCtrlTestmodeOneShot;
      default: `uvm_fatal(`gfn, "Should never happen")
    endcase
    cov.adc_ctrl_testmode_cg.sample(testmode);
  endfunction

  // Process ADC CTRL filter model data
  virtual function void process_filter_data(int channel, adc_value_logic_t val,
                                            bit call_debounce = 1);
    bit filter_match;
    // Perform the basic match against filter config
    for (int filter_idx = 0; filter_idx < ADC_CTRL_NUM_FILTERS; filter_idx++) begin
      // Extract appropriate configuration for this channel/filter
      adc_ctrl_filter_cfg_t filter_cfg = cfg.filter_cfg[channel][filter_idx];
      // Check value against configured range of values
      bit inside_range = val inside {[filter_cfg.min_v : filter_cfg.max_v]};
      // Set match flag for this channel/filter considering inside/outside config
      m_chn_match[channel][filter_idx] = (filter_cfg.cond == ADC_CTRL_FILTER_COND_IN) ?
          inside_range : ~inside_range;

      // Combine channel matches for this filter
      filter_match = 0;
      for (int channel_idx = 0; channel_idx < ADC_CTRL_CHANNELS; channel_idx++) begin
        filter_match |= cfg.filter_cfg[channel_idx][filter_idx].en;
      end

      for (int channel_idx = 0; channel_idx < ADC_CTRL_CHANNELS; channel_idx++) begin
        filter_match &= !cfg.filter_cfg[channel_idx][filter_idx].en |
			 (m_chn_match[channel_idx][filter_idx] &
			  cfg.filter_cfg[channel_idx][filter_idx].en);
      end
      m_match[filter_idx] = filter_match;
    end

    // If this was data from the last channel process debounce model
    if (call_debounce && channel == (ADC_CTRL_CHANNELS - 1)) process_debounce();
  endfunction

  // Process debounce
  // From the spec:
  // All pairs of filters that are enabled in adc_chn0_filter_ctl[7:0] and adc_chn1_filter_ctl[7:0]
  // are evaluated after each pair of samples has been taken. The filter result is passed to the
  // periodic scan counter if enabled and not at its limit otherwise the result is passed to the
  // debounce counter. The list below describes how the counters interpret the filter results:
  // If no filters are hit then the counter will reset to zero.
  // If one or more filters are hit but the set hit differs from the previous evaluation the
  // counter resets to zero.
  // If one or more filters are hit and either none was hit in the previous evaluation or the same
  // set was hit in the previous evaluation and the counter is not at its threshold then the
  // counter will increment.
  // If one or more filters are hit and the same set was hit in the previous evaluation and the
  // counter is at its threshold then the counter stays at the threshold.
  // If the counter is the periodic scan counter and it reaches its threshold, as defined by
  // adc_lp_sample_ctl.lp_sample_cnt, then continuous scanning is enabled and the debounce counter
  // will be used for future evaluations.
  // If the counter is the debounce counter and it reaches its threshold, as defined by
  // adc_sample_ctl.np_sample_cnt, then:
  // An interrupt is raised if the threshold is met for the first time.
  // The current sample values are latched into adc_chn_val[0].adc_chn_value_intr and
  // adc_chn_val[1].adc_chn_value_intr.
  // If a series of interrupts and matches are seen, these registers only record the value
  // of the last debounced hit.
  // The adc_intr_status register is updated by setting the bits corresponding to filters that
  // are hit (note that bits that are already set will not be cleared). This will cause the block
  // to raise an interrupt if it was not already doing so.
  // If a filter is a hit and is also enabled in adc_wakeup_ctl the corresponding filter
  // generates a wakeup.
  // Note that the debounce counter will remain at its threshold until the set of filters are
  // changed by software to debounce a different event or if the current match changes.
  // This implies that a stable matching event continuously matches until some condition in the
  // system (changed filter settings or changed ADC output) alters the result.
  // Because scanning continues the adc_intr_status register will reflect any debounced events
  // that are detected between the controller raising an interrupt and the status bits being
  // cleared (by having 1 written to them). However, the adc_chn_val[0].adc_chn_value_intr and
  // adc_chn_val[1].adc_chn_value_intrregisters record the value at the time the interrupt was
  // first raised and thus reflect the filter state from that point.

  virtual function void process_debounce();
    // Select debounce mode
    if (cfg.testmode inside {AdcCtrlTestmodeNormal, AdcCtrlTestmodeLowpower}) begin
      if (!m_lp_mode) process_np_debounce();  // Normal power
      else process_lp_debounce();  // Low power
    end

    // Implement One Shot Mode
    // One hot interrupt is one bit above the last filter's interrupt
    if (cfg.testmode inside {AdcCtrlTestmodeOneShot}) begin
      m_expected_adc_intr_status[ADC_CTRL_NUM_FILTERS] = cfg.adc_intr_ctl[ADC_CTRL_NUM_FILTERS];
      m_expected_intr_state |= cfg.adc_intr_ctl[ADC_CTRL_NUM_FILTERS];
    end

    // Delayfor edge detection
    m_match_prev = m_match;

    // Decode expected wakeup - allow dynamic control
    m_expected_wakeup = |(m_expected_filter_status & cfg.ral.adc_wakeup_ctl.get_mirrored_value());
  endfunction

  // Process normal power debounce
  virtual function void process_np_debounce();
    if (m_match != 0 && !m_adc_fsm_reset) begin
      if ((m_match == m_match_prev) || (m_match_prev == 0)) begin
        // If one or more filters are hit and either none was hit in the previous evaluation
        // or the same set was hit in the previous evaluation and the counter is not
        // at its limit then the counter will increment.
        if (m_np_counter < cfg.np_sample_cnt) begin
          // Not at it's limit
          m_np_counter++;
          // Note m_np_counter has now been incremented below so we can detect the
          // transition from (cfg.np_sample_cnt - 1) to cfg.np_sample_cnt
          if (m_np_counter == cfg.np_sample_cnt && !m_debounced) begin
            // Capture matches
            m_debounced = 1;
            m_expected_filter_status |= m_match;
            m_expected_adc_intr_status |= m_match & cfg.adc_intr_ctl;
            m_expected_intr_state |= (|(m_match & cfg.adc_intr_ctl));

            // Update interrupt ADC values
            foreach (m_adc_latest_values[channel]) begin
              m_adc_interrupt_values[channel] = m_adc_latest_values[channel];
            end

          end
        end
      end else begin
        // Previous matched set different to current
        m_np_counter = 0;
        m_debounced  = 0;
      end
    end else begin
      // No filters hit
      m_np_counter = 0;
      m_debounced  = 0;
    end
  endfunction

  // Process low power debounce
  virtual function void process_lp_debounce();
    if (m_match != 0 && !m_adc_fsm_reset) begin
      if ((m_match == m_match_prev) || (m_match_prev == 0)) begin
        // If one or more filters are hit and either none was hit in the previous evaluation
        // or the same set was hit in the previous evaluation and the counter is not
        // at its limit then the counter will increment.
        if (m_lp_counter < cfg.lp_sample_cnt) begin
          // Not at it's limit
          m_lp_counter++;
          // Note m_lp_counter has now been incremented below so we can detect the
          // transition from (cfg.lp_sample_cnt - 1) to cfg.lp_sample_cnt
          if (m_lp_counter == cfg.lp_sample_cnt) begin
            // Move to normal power mode
            m_lp_mode = 0;
            // Reflect in config object
            cfg.lp_mode = 0;
            m_lp_counter = 0;
          end
        end
      end else begin
        // Previous matched set different to current
        m_lp_counter = 0;
      end
    end else begin
      // No filters hit
      m_lp_counter = 0;
    end
  endfunction


  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    // Latest values
    m_adc_latest_values.delete();
    m_adc_interrupt_values.delete();
    // Clear all match flags
    m_match = 0;
    m_match_prev = 0;
    m_chn_match = 0;
    m_np_counter = 0;
    m_lp_counter = 0;
    m_debounced = 0;
    m_expected_filter_status = 0;
    m_expected_adc_intr_status = 0;
    m_expected_intr_state = 0;
    m_adc_ctrl_en = 0;
    m_lp_mode = 0;
  endfunction

  // Software reset
  // val = register value
  virtual function void do_adc_fsm_reset(bit val);
    m_adc_fsm_reset = val;
    if (val) begin
      // Clear model state
      m_np_counter = 0;
      m_lp_counter = 0;
      m_debounced = 0;
      m_lp_mode = 0;
    end
  endfunction


  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
