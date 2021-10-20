// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Send a random ramp to each of the ADC channels 
// using ast_adc_all_random_seq as a subsequence
class ast_adc_random_ramp_seq extends ast_adc_base_seq ;
  
  // Minimum value of the ramp
  rand int  ramp_min;
  // Maximum value of the ramp
  rand int  ramp_max;
  // Direction 1=rising 0=falling
  rand bit  ramp_rising;
  // Minimum ramp step 
  rand int  ramp_step_min;
   // Maximum ramp step 
  rand int  ramp_step_max;

  // Current values for the channels
  int  current_values [AdcChannels];
  
  `uvm_object_utils_begin(ast_adc_random_ramp_seq)
    `uvm_field_int(ramp_min, UVM_DEFAULT)
    `uvm_field_int(ramp_max, UVM_DEFAULT)
    `uvm_field_int(ramp_rising, UVM_DEFAULT) 
    `uvm_field_int(ramp_step_min, UVM_DEFAULT)
    `uvm_field_int(ramp_step_max, UVM_DEFAULT)
    `uvm_field_sarray_int(current_values, UVM_DEFAULT)
  `uvm_object_utils_end
 
  `uvm_object_new

  // Check for valid inputs
  constraint valid_c {
    ramp_step_min > 0;
    ramp_min inside { [ 0 : (1 << AdcDataWidth)] };
    ramp_max inside { [ 0 : (1 << AdcDataWidth)] };
    ramp_max >= ramp_min;
  }


  virtual task body();
    //const int unsigned ramp_start = ramp_rising ? ramp_min : ramp_max;
    //const int unsigned ramp_end   = ramp_rising ? ramp_max : ramp_min;
    bit all_ended;

    // Set current values set to starting value
    foreach(current_values[channel]) 
      current_values[channel]=ramp_rising ? ramp_min : ramp_max;
  
    // Send starting values via subsequence
    `uvm_do_with(m_ast_adc_all_random_seq, {
            foreach( data[channel] ) {
            data[channel] == local::current_values[channel];
          }
        })
  
    `uvm_info(`gfn, m_ast_adc_all_random_seq.sprint(), UVM_HIGH)

    // Increment or decrement the ADC channel data until 
    // we reach the end values for all channels
    while(current_values.or() with 
        (ramp_rising ? (item < ramp_max) : (item > ramp_min))) begin

      `uvm_do_with(m_ast_adc_all_random_seq, {

        // Set the values
        foreach( data[channel] ) {
          if(local::ramp_rising) {
            // Rising ramp
            // Set absolute maximum range
            data[channel] inside {[ current_values[channel]  : local::ramp_max]};

            // Set increment range use soft constraint to allow for fail 
            // if we are near or at the end
            soft data[channel] inside {
                [ local::current_values[channel] + local::ramp_step_min : 
                    local::current_values[channel] + local::ramp_step_max ]
                };
          } else {
            // Falling ramp
            // Set absolute maximum range
            data[channel] inside {[ local::ramp_min : current_values[channel] ]};

            // Set decrement range use soft constraint to allow for fail 
            // if we are near or at the end
            soft data[channel] inside {
                [ local::current_values[channel] - local::ramp_step_max : 
                    local::current_values[channel] - local::ramp_step_min ]
                };
          }
        }
      })
      
      `uvm_info(`gfn, m_ast_adc_all_random_seq.sprint(), UVM_HIGH)

      // Copy sent values to our current values
      foreach(current_values[channel]) 
        current_values[channel] = m_ast_adc_all_random_seq.data[channel];

    end

  endtask

endclass
