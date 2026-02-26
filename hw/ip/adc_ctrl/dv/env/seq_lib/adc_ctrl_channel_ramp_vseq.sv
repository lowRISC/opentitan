// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A ramp virtual sequence that controls an ADC channel, ramping between two values. This is a
// virtual sequence because it works entirely by controlling an existing push_pull sequence through
// a config object.

class adc_ctrl_channel_ramp_vseq extends uvm_sequence;
  // A config object for the push/pull agent through which we will control the ADC channel
  adc_push_pull_config_t push_pull_cfg;
  // An event that the environment will trigger when a push/pull item is received on this channel.
  event push_pull_ev;

  // Start value of the ramp
  rand adc_value_t ramp_start;
  // End value of the ramp
  rand adc_value_t ramp_end;
  // Minimum ramp step
  rand int unsigned ramp_step_min;
  // Maximum ramp step
  rand int unsigned ramp_step_max;

  // Constrain the ramp start and end values to be less than (1 << ADC_CTRL_DATA_WIDTH). Constrain
  // the range of step sizes (ensuring that they are bounded above by ramp_step_max, which means
  // we're unlikely to jump the whole way in one go).
  extern constraint ramp_constraints_c;

  extern function new(string name="");
  extern task body();
  extern task send_adc_data(adc_value_t value);

  `uvm_object_utils_begin(adc_ctrl_channel_ramp_vseq)
    `uvm_field_int(ramp_start, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(ramp_end, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(ramp_step_min, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(ramp_step_max, UVM_DEFAULT | UVM_DEC)
  `uvm_object_utils_end
endclass

constraint adc_ctrl_channel_ramp_vseq::ramp_constraints_c {
  ramp_start < (1 << ADC_CTRL_DATA_WIDTH);
  ramp_end < (1 << ADC_CTRL_DATA_WIDTH);

  1 <= ramp_step_max;
  ramp_step_min <= ramp_step_max;
}

function adc_ctrl_channel_ramp_vseq::new(string name="");
  super.new(name);
endfunction

task adc_ctrl_channel_ramp_vseq::body();
  // Current value for the channel (starts at the starting value)
  adc_value_t current_value = ramp_start;

  // Send the starting value through the push/pull agent
  send_adc_data(current_value);

  // Increment/decrement the ADC channel data until we get to the end value
  while (current_value != ramp_end) begin
    // Pick a random ramp step size in [ramp_step_min:ramp_step_max].
    int unsigned ramp_step = $urandom_range(ramp_step_min, ramp_step_max);

    // Update the current value of the ramp accordingly, clamping to ramp_end
    if (current_value < ramp_end) begin
      current_value += min2(ramp_step, ramp_end - current_value);
    end else begin
      current_value -= min2(ramp_step, current_value - ramp_end);
    end

    // Send next data via ADC bus
    send_adc_data(current_value);
  end
endtask

task adc_ctrl_channel_ramp_vseq::send_adc_data(adc_value_t value);
  push_pull_cfg.clear_d_user_data();
  push_pull_cfg.add_d_user_data(value);

  // Wait to be told that data was received (via the scoreboard)
  @push_pull_ev;
endtask
