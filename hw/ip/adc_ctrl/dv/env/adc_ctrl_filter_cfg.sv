// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The configuration for a single filter

class adc_ctrl_filter_cfg extends uvm_object;
  // An interval of values (inclusive).
  rand bit [ADC_CTRL_DATA_WIDTH-1:0] min_v;
  rand bit [ADC_CTRL_DATA_WIDTH-1:0] max_v;

  // If match_outside is true, the filter matches a value iff it is not in [min_v, max_v]. If not,
  // the filter matches a value iff it is *inside* [min_v, max_v].
  rand bit match_outside;

  // Control whether the filter is enabled
  rand bit enabled;

  `uvm_object_utils_begin(adc_ctrl_filter_cfg)
    `uvm_field_int(min_v,        UVM_DEFAULT)
    `uvm_field_int(max_v,        UVM_DEFAULT)
    `uvm_field_int(match_outside, UVM_DEFAULT)
    `uvm_field_int(enabled,      UVM_DEFAULT)
  `uvm_object_utils_end

  // Ensure that min_v <= max_v
  extern constraint min_le_max_c;

  extern function new (string name="");

  // A static factory method that returns a filter with the range [min_v, max_v] and the
  // given match_outside / enabled values.
  extern static function adc_ctrl_filter_cfg make(string                        name,
                                                  bit [ADC_CTRL_DATA_WIDTH-1:0] min_v,
                                                  bit [ADC_CTRL_DATA_WIDTH-1:0] max_v,
                                                  bit                           match_outside,
                                                  bit                           enabled = 1'b1);
endclass

constraint adc_ctrl_filter_cfg::min_le_max_c {
  min_v <= max_v;
}

function adc_ctrl_filter_cfg::new (string name="");
  super.new(name);
endfunction

function adc_ctrl_filter_cfg
  adc_ctrl_filter_cfg::make(string                        name,
                            bit [ADC_CTRL_DATA_WIDTH-1:0] min_v,
                            bit [ADC_CTRL_DATA_WIDTH-1:0] max_v,
                            bit                           match_outside,
                            bit                           enabled = 1'b1);
  adc_ctrl_filter_cfg ret;

  if (max_v < min_v) begin
    `uvm_fatal("adc_ctrl_filter_cfg::make",
               $sformatf("Backwards min_v/max_v range of [%0x, %0x]", min_v, max_v))
  end

  ret = adc_ctrl_filter_cfg::type_id::create(name);
  ret.min_v = min_v;
  ret.max_v = max_v;
  ret.match_outside = match_outside;
  ret.enabled = enabled;
  return ret;
endfunction
