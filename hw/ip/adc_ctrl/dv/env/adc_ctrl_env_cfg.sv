// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_env_cfg extends cip_base_env_cfg #(
  .RAL_T(adc_ctrl_reg_block)
);

  virtual clk_rst_if clk_aon_rst_vif;

  // ext component cfgs
  ast_adc_agent_cfg m_ast_adc_agent_cfg;

  // Test configuration

  // Basic testing mode
  adc_ctrl_testmode_e testmode;

  // Index of interrupt 
  rand int unsigned intr_idx;

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
      `uvm_field_int(pwrup_time, UVM_DEFAULT)
      `uvm_field_int(wakeup_time, UVM_DEFAULT)
      `uvm_field_int(np_sample_cnt, UVM_DEFAULT)
      `uvm_field_int(lp_sample_cnt, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = adc_ctrl_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    // create AST ADC agent config obj
    m_ast_adc_agent_cfg = ast_adc_agent_cfg::type_id::create("m_ast_adc_agent_cfg");

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

  // Constraints
   // Set the size of the filter_cfg array
  constraint  filter_cfg_size_c {
    // Size of first dimension
    filter_cfg.size == AdcCtrlChannels;

    // Size of second dimension
    foreach(filter_cfg[channel]){
      filter_cfg[channel].size == AdcCtrlFilters;
    }

  }

  // Valid values
  constraint  valid_c {
    pwrup_time  inside {[0 : 2**4 - 1]};
    wakeup_time inside {[0 : 2**24 - 1]};
    np_sample_cnt inside {[0 : 2**16 - 1]};
    lp_sample_cnt inside {[0 : 2**8 - 1]};
  }

  // Test defaults
  constraint  defaults_c {
    // Default interrupt index
    soft intr_idx == 0;

    // Power / wake up - different values to reset
    soft pwrup_time   == 5;
    soft wakeup_time  == 1599;
    // Debouncing sample counts for normal and low power mode - different values to reset
    soft np_sample_cnt == 111;
    soft lp_sample_cnt == 3;
    

    // Default filter configuration
    // This is the one assumed for normal use
    foreach(filter_cfg[channel]) {
      foreach(filter_cfg[channel][filter]) {
        soft filter_cfg[channel][filter] == FilterCfgDefaults[filter];
      }
    }
  }

  // do_print, do_copy etc for types unsupported by the macros

  virtual function void do_print( uvm_printer printer);
    // These shoud come first
    super.do_print( printer );

    // Implement filter_cfg - 2d array of structs
    printer.print_array_header("filter_cfg", filter_cfg.size);
    for(int channel = $low(filter_cfg); channel <= $high(filter_cfg); channel++) begin
      printer.print_array_header($sformatf("filter_cfg[%0d]",channel), filter_cfg[channel].size());
      for(int filter = $low(filter_cfg[channel]); filter <= $high(filter_cfg[channel]); filter++) begin
        printer.print_generic(
            $sformatf("filter_cfg[%0d][%0d]",channel,filter),
            "adc_ctrl_filter_cfg_t",
            $bits(filter_cfg[channel][filter]),
            $sformatf("%p", filter_cfg[channel][filter])
            );
      end
      printer.print_array_footer();        
    end
    printer.print_array_footer(); 



  endfunction

  virtual function void do_copy (uvm_object rhs);
      type_id::T rhs_; // type_id::T == this class (set in `uvm_object_utils)
      super.do_copy(rhs);
      $cast(rhs_,rhs);

      // Implement filter_cfg
      filter_cfg = rhs_.filter_cfg;
  endfunction

endclass
