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
  protected adc_value_logic_t m_adc_latest_values[int];

  // Interrupt value for each channel
  protected adc_value_logic_t m_adc_interrupt_values[int];

  // Interrupt line
  protected logic m_interrupt, m_interrupt_prev;

  // ADC Model variables
  // Filter match for each filter of each channel
  protected bit [ADC_CTRL_CHANNELS - 1 : 0][ADC_CTRL_NUM_FILTERS-1 : 0] m_chn_match;
  // Combined matches from all channels
  protected bit [ADC_CTRL_NUM_FILTERS-1 : 0] m_match, m_match_prev;
  // Normal power and low power sample match counters
  protected uint16_t m_np_counter, m_lp_counter;
  // Expected filter status bits
  protected
  bit [ADC_CTRL_NUM_FILTERS - 1 : 0]
      m_expected_filter_status, m_expected_filter_status_prev;
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
  endfunction

  task run_phase(uvm_phase phase);
    int idx = 0;
    super.run_phase(phase);
    fork
      monitor_intr_proc();
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
    forever begin
      cfg.clk_aon_rst_vif.wait_clks(1);
      m_interrupt_prev = m_interrupt;
      m_interrupt = cfg.intr_vif.sample_pin(ADC_CTRL_INTERRUPT_INDEX);

      // If we see a positive edge on the interrupt line capture the latest values
      if (m_interrupt & ~m_interrupt_prev) begin
        foreach (m_adc_latest_values[channel]) begin
          m_adc_interrupt_values[channel] = m_adc_latest_values[channel];
        end
      end

      // Compare against expected every change of interrupt line
      if (cfg.en_scb & (m_interrupt ^ m_interrupt_prev)) begin
        `uvm_info(`gfn, $sformatf(
                  "monitor_intr_proc: interrupt pin change m_interrupt=%b", m_interrupt),
                  UVM_MEDIUM)
        `DV_CHECK_EQ(m_interrupt, m_expected_intr_state)
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

      // Send data to filter model
      process_filter_data(channel, item.d_data);

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
        // TODO: update modeling for One Shot mode
        do_read_check = !(cfg.testmode inside {AdcCtrlOneShot});
        if (addr_phase_write) begin
          ->m_intr_state_wr_ev;
          // Implement W1C
          m_expected_intr_state &= (~item.a_data);
        end
        if (addr_phase_read) begin
          `DV_CHECK(csr.predict(.value(m_expected_intr_state), .kind(UVM_PREDICT_READ)))
        end
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
        // FIXME
      end
      "adc_intr_status": begin
        // TODO: update modeling for One Shot mode
        do_read_check = !(cfg.testmode inside {AdcCtrlOneShot});
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
      "adc_en_ctl": begin
        // FIXME
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
          // Update m_expected_filter_status_prev after 1 clock
          fork
            begin
              cfg.clk_aon_rst_vif.wait_clks(1);
              m_expected_filter_status_prev = m_expected_filter_status;
            end
          join_none
        end

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
            `uvm_info(`gfn, "FIXME: Predict adc_chn_val_0.adc_chn_value_intr", UVM_NONE)
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
            `uvm_info(`gfn, "FIXME: Predict adc_chn_val_1.adc_chn_value_intr", UVM_NONE)
          end
        end
      end


      default: begin
        //`uvm_error(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, $sformatf(
                     "reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  // Process ADC CTRL filter model data
  virtual function void process_filter_data(int channel, adc_value_logic_t val);
    bit filter_match;
    // Perform the basic match against filter config
    for (int filter_idx = 0; filter_idx < ADC_CTRL_NUM_FILTERS; filter_idx++) begin
      // Extract appropriate configuration for this channel/filter
      adc_ctrl_filter_cfg_t filter_cfg = cfg.filter_cfg[channel][filter_idx];
      // Check value against configured range of values
      bit inside_range = val inside {[filter_cfg.min_v : filter_cfg.max_v]};
      // Set match flag for this channel/filter considering inside/outside config
      m_chn_match[channel][filter_idx] = (filter_cfg.cond == ADC_CTRL_FILTER_IN) ?
          inside_range : ~inside_range;

      // Combine channel matches for this filter
      filter_match = 1;
      for (int channel_idx = 0; channel_idx < ADC_CTRL_CHANNELS; channel_idx++) begin
        filter_match &= (m_chn_match[channel_idx][filter_idx] &
            cfg.filter_cfg[channel_idx][filter_idx].en);
      end
      m_match[filter_idx] = filter_match;
    end

    // If this was data from the last channel process debounce model
    if (channel == (ADC_CTRL_CHANNELS - 1)) process_debounce();
  endfunction

  // Process debounce
  // From the spec:
  // All pairs of filters that are enabled in adc_chn0_filter_ctl[7:0] and adc_chn1_filter_ctl[7:0] are evaluated
  // after each pair of samples has been taken. The filter result is passed to the periodic scan counter if enabled and not at its limit
  // otherwise the result is passed to the debounce counter. The list below describes how the counters interpret the filter results:
  // If no filters are hit then the counter will reset to zero.
  // If one or more filters are hit but the set hit differs from the previous evaluation the counter resets to zero.
  // If one or more filters are hit and either none was hit in the previous evaluation or the same set was hit in the previous
  // evaluation and the counter is not at its limit then the counter will increment.
  // If the counter is the periodic scan counter and it reaches its limit then continuous scanning is enabled and the debounce
  // counter will be used for future evaluations.
  // If the counter is the debounce counter and it reaches its limit then:
  // If an interrupt is not already being raised then the current sample values are latched into adc_chn_val[0].adc_chn_value_intr
  // and adc_chn_val[1].adc_chn_value_intr. i.e. these registers only record the value of the first debounced hit.
  // The adc_intr_status register is updated by setting the bits corresponding to filters that are hit (note that bits that
  // are already set will not be cleared). This will cause the block to raise an interrupt if it was not already doing so.
  // If any filters are hit that are enabled in adc_wakeup_ctl the corresponding bits in the adc_wakeup_status register are set
  // which may initiate a wakeup.
  // Note that the debounce counter will remain at its limit until the set of filters that are set changes when it will be
  // reset to zero and start to debounce the next event.

  virtual function void process_debounce();
    if (m_match != 0) begin
      if ((m_match == m_match_prev) || (m_match_prev == 0)) begin
        // If one or more filters are hit and either none was hit in the previous evaluation
        // or the same set was hit in the previous evaluation and the counter is not
        // at its limit then the counter will increment.
        if (m_np_counter < (cfg.np_sample_cnt - 1)) begin
          // Not at it's limit
          m_np_counter++;
        end else if (!m_debounced) begin
          bit intr_enable = ral.intr_enable.debug_cable.get_mirrored_value();
          // Capture matches
          m_debounced = 1;
          m_expected_filter_status |= m_match;
          m_expected_adc_intr_status |= (m_expected_filter_status & ~m_expected_filter_status_prev);
          m_expected_intr_state = intr_enable & (|(m_expected_adc_intr_status & cfg.adc_intr_ctl));
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
    // Delayfor edge detection
    m_match_prev = m_match;
    m_expected_filter_status_prev = m_expected_filter_status;
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
    m_expected_filter_status = 0;
    m_expected_filter_status_prev = 0;
    m_expected_adc_intr_status = 0;
    m_expected_intr_state = 0;
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
