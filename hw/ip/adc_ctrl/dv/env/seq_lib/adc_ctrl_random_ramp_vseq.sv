// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Send a random ramp to each of the ADC channels
class adc_ctrl_random_ramp_vseq extends adc_ctrl_base_vseq;

  // Minimum value of the ramp
  rand int ramp_min;
  // Maximum value of the ramp
  rand int ramp_max;
  // Direction 1=rising 0=falling
  rand bit ramp_rising;
  // Minimum ramp step
  rand int ramp_step_min;
  // Maximum ramp step
  rand int ramp_step_max;


  // Current values for the channels
  adc_value_t current_values[ADC_CTRL_CHANNELS];
  // Next values for the channels
  adc_value_t next_values[ADC_CTRL_CHANNELS];
  // Increment/decrement value for this step
  int ramp_step[ADC_CTRL_CHANNELS];

  `uvm_object_utils_begin(adc_ctrl_random_ramp_vseq)
    `uvm_field_int(ramp_min, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(ramp_max, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(ramp_rising, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(ramp_step_min, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(ramp_step_max, UVM_DEFAULT | UVM_DEC)
    `uvm_field_sarray_int(current_values, UVM_DEFAULT | UVM_DEC)
    `uvm_field_sarray_int(next_values, UVM_DEFAULT | UVM_DEC)
    `uvm_field_sarray_int(ramp_step, UVM_DEFAULT | UVM_DEC)
  `uvm_object_utils_end

  `uvm_object_new

  // Check for valid inputs
  constraint valid_c {
    ramp_step_min inside {[0 : $]};
    ramp_step_max inside {[1 : $]};
    ramp_step_max >= ramp_step_min;
    ramp_min inside {[0 : (1 << ADC_CTRL_DATA_WIDTH) - 1]};
    ramp_max inside {[0 : (1 << ADC_CTRL_DATA_WIDTH) - 1]};
    ramp_max >= ramp_min;
  }

  virtual task pre_start();
    do_adc_ctrl_init = 0;
    do_dut_init = 0;
    super.pre_start();
  endtask

  virtual task post_start();
    // Don't do anything after the sequence ends
  endtask

  virtual task body();
    bit all_ended;

    // Set current values set to starting value
    foreach (current_values[channel]) current_values[channel] = ramp_rising ? ramp_min : ramp_max;

    // Send via push pull agents
    send_adc_data(current_values);
    `uvm_info(`gfn, this.sprint(uvm_default_line_printer), UVM_MEDIUM)

    // Increment or decrement the ADC channel data until
    // we reach the end values for all channels
    while(current_values.or() with
        (ramp_rising ? (int'(item) < ramp_max) : (int'(item) > ramp_min))) begin

      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(ramp_step,
                                         foreach(ramp_step[channel]) {
          ramp_step[channel] inside {[ramp_step_min : ramp_step_max]};
        })

      foreach (next_values[channel]) begin
        if (ramp_rising) begin
          next_values[channel] =
              min2((int'(current_values[channel]) + ramp_step[channel]), ramp_max);
        end else begin
          next_values[channel] =
              max2((int'(current_values[channel]) - ramp_step[channel]), ramp_min);
        end
      end

      `uvm_info(`gfn, this.sprint(uvm_default_line_printer), UVM_MEDIUM)

      // Send next data via ADC bus
      send_adc_data(next_values);

      // Copy next values to current values
      foreach (current_values[channel]) current_values[channel] = next_values[channel];

    end

  endtask

  task send_adc_data(adc_value_t data[ADC_CTRL_CHANNELS]);
    `uvm_info(`gfn, $sformatf("send_adc_data: data=%p", data), UVM_MEDIUM)

    foreach (data[channel]) begin
      cfg.m_adc_push_pull_cfg[channel].clear_d_user_data();
      cfg.m_adc_push_pull_cfg[channel].add_d_user_data(data[channel]);
    end

    // Wait for data to be received by the scoreboard
    wait_all_rx();

  endtask

endclass
