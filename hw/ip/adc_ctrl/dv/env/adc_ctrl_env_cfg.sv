// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_env_cfg extends cip_base_env_cfg #(
  .RAL_T(adc_ctrl_reg_block)
);
  virtual clk_rst_if clk_aon_rst_vif;
  wakeup_vif_t wakeup_vif;

  // ADC push pull agent configs
  adc_push_pull_config_t m_adc_push_pull_cfg[ADC_CTRL_CHANNELS];
  // Events triggered by scoreboard when a push pull item is received
  event m_adc_push_pull_ev[ADC_CTRL_CHANNELS];

  // Test configuration

  // If set use the same filter configuration each iteration
  bit filters_fixed = 0;

  // Basic testing mode
  adc_ctrl_testmode_e testmode;
  // Model in low power mode
  bit lp_mode;

  // Interrupt control bits
  bit [ADC_CTRL_NUM_FILTERS:0] adc_intr_ctl = 0;

  // Wakeup control bits
  bit [ADC_CTRL_NUM_FILTERS-1:0] adc_wakeup_ctl = 0;

  // For longtest, adjust large time value to avoid test timeout
  bit                           fast_mode = 0;

  // Power up / wake up time
  rand int pwrup_time;
  rand int wakeup_time;

  // Filter values filter_cfg[channel][filter]
  rand adc_ctrl_filter_cfg_t filter_cfg[][];

  // Debouncing sample counts for normal and low power modes
  rand int np_sample_cnt;
  rand int lp_sample_cnt;

  `uvm_object_utils_begin(adc_ctrl_env_cfg)
    `uvm_field_enum(adc_ctrl_testmode_e, testmode, UVM_DEFAULT)
    `uvm_field_int(filters_fixed, UVM_DEFAULT)
    `uvm_field_int(pwrup_time, UVM_DEFAULT)
    `uvm_field_int(wakeup_time, UVM_DEFAULT)
    `uvm_field_int(np_sample_cnt, UVM_DEFAULT)
    `uvm_field_int(lp_sample_cnt, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = adc_ctrl_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
    // Create ADC push pull agent configs
    for (int idx = 0; idx < ADC_CTRL_CHANNELS; idx++) begin
      string name = $sformatf("m_adc_push_pull_cfg_%0d", idx);
      m_adc_push_pull_cfg[idx] = adc_push_pull_config_t::type_id::create(name);
      m_adc_push_pull_cfg[idx].if_mode = Device;
      m_adc_push_pull_cfg[idx].agent_type = push_pull_agent_pkg::PullAgent;
      m_adc_push_pull_cfg[idx].pull_handshake_type = push_pull_agent_pkg::FourPhase;

      // We never want zero delays for the ADC as this is not possible
      `DV_CHECK_RANDOMIZE_WITH_FATAL(m_adc_push_pull_cfg[idx],
                                     zero_delays      == 0;
          ack_lo_delay_min == 1;
          ack_lo_delay_max == 2;
          req_lo_delay_min == 1;
          req_lo_delay_max == 2;
          device_delay_min == 12;
          device_delay_max == 16;)
    end

    // set num_interrupts & num_alerts
    num_interrupts = ral.intr_state.get_n_used_bits();

    // only support 1 outstanding TL item
    m_tl_agent_cfg.max_outstanding_req = 1;

  endfunction

  // Constraints
  // Set the size of the filter_cfg array
  constraint filter_cfg_size_c {
    // Size of first dimension
    filter_cfg.size == ADC_CTRL_CHANNELS;

    // Size of second dimension
    foreach (filter_cfg[channel]) {filter_cfg[channel].size == ADC_CTRL_NUM_FILTERS;}

  }

  // Valid values
  constraint valid_c {
    pwrup_time inside {[0 : 2 ** 4 - 1]};
    wakeup_time inside {[0 : 2 ** 24 - 1]};
    np_sample_cnt inside {[1 : 2 ** 16 - 1]};
    lp_sample_cnt inside {[1 : 2 ** 16 - 1]};
  }


  // Test defaults
  constraint defaults_c {

    // Power / wake up - different values to reset
    soft pwrup_time == 5;
    soft wakeup_time == 11;
    // Debouncing sample counts for normal and low power mode - different values to reset
    soft np_sample_cnt inside {[3 : 7]};
    soft lp_sample_cnt inside {[3 : 7]};

    // Default filter configuration
    // This is the one assumed for normal use
    foreach (filter_cfg[channel]) {
      foreach (filter_cfg[channel][filter]) {
        soft filter_cfg[channel][filter] == FILTER_CFG_DEFAULTS[filter];
      }
    }
  }

  // Wait for an ADC push pull item received event.
  virtual task wait_adc_rx_event(int channel);
    @(m_adc_push_pull_ev[channel]);
  endtask

  // Trigger an ADC push pull item received event.
  virtual function void trigger_adc_rx_event(int channel);
    ->m_adc_push_pull_ev[channel];
  endfunction

  // do_print, do_copy etc for types unsupported by the macros

  virtual function void do_print(uvm_printer printer);
    // These shoud come first
    super.do_print(printer);

    // Implement filter_cfg - 2d array of structs
    printer.print_array_header("filter_cfg", filter_cfg.size);
    for (int channel = $low(filter_cfg); channel <= $high(filter_cfg); channel++) begin
      printer.print_array_header($sformatf("filter_cfg[%0d]", channel), filter_cfg[channel].size());
      for (
          int filter = $low(filter_cfg[channel]); filter <= $high(filter_cfg[channel]); filter++
      ) begin
        printer.print_generic($sformatf("filter_cfg[%0d][%0d]", channel, filter),
                              "adc_ctrl_filter_cfg_t", $bits(filter_cfg[channel][filter]),
                              $sformatf("%p", filter_cfg[channel][filter]));
      end
      printer.print_array_footer();
    end
    printer.print_array_footer();
  endfunction

  virtual function void do_copy(uvm_object rhs);
    type_id::T rhs_;  // type_id::T == this class (set in `uvm_object_utils)
    super.do_copy(rhs);
    $cast(rhs_, rhs);

    // Implement filter_cfg
    filter_cfg = rhs_.filter_cfg;
  endfunction

endclass
