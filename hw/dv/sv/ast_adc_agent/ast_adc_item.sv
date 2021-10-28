// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ast_adc_item extends uvm_sequence_item;

  // random variables

  // ADC channel
  rand uint channel;
  // Data for the respective channel of the ADC
  rand ast_adc_value_logic_t  data;

  `uvm_object_utils_begin(ast_adc_item)
    `uvm_field_int(channel, UVM_DEFAULT)
    `uvm_field_int(data,    UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  constraint channel_c {
    channel inside {[0 : AdcChannels-1]};
  }
endclass
