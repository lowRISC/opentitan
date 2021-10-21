// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ast_adc_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  // Imports from AST package
  import ast_pkg::AdcChannels, ast_pkg::AdcDataWidth;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // local types
  // forward declare classes to allow typedefs below
  typedef class ast_adc_item;
  typedef class ast_adc_agent_cfg;

  // Forward declarations for sequences
  typedef class ast_adc_all_random_seq;
  typedef class ast_adc_random_ramp_seq;

  // reuse dv_base_sequencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T(ast_adc_item),
                              .CFG_T (ast_adc_agent_cfg)) ast_adc_sequencer;

  // functions

  // Number of ADC channels
  // parameter int AdcChannels     = 2;
  // Width of ADC data
  // parameter int AdcDataWidth    = 10;
  // Maximum outstanding transactions
  parameter int MaxOutstandingTrans = 4;

  // Single ADC value
  typedef logic unsigned [AdcDataWidth - 1 : 0] ast_adc_value_t;
  // Logic version of above
  typedef bit unsigned [AdcDataWidth - 1 : 0] ast_adc_value_logic_t;
  // Static array of ADC values for all the channels
  typedef ast_adc_value_t ast_adc_value_sarray_t [ AdcChannels ];
  // Logic version of above
  typedef ast_adc_value_logic_t ast_adc_value_logic_sarray_t [ AdcChannels ];

  // Dynamic array of ADC values
  typedef ast_adc_value_t ast_adc_value_array_t [];

  // package sources
  `include "ast_adc_item.sv"
  `include "ast_adc_agent_cfg.sv"
  `include "ast_adc_agent_cov.sv"
  `include "ast_adc_driver.sv"
  `include "ast_adc_monitor.sv"
  `include "ast_adc_agent.sv"
  `include "ast_adc_seq_list.sv"

endpackage: ast_adc_agent_pkg
