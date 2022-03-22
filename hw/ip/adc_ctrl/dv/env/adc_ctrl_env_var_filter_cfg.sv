// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Environment config extended for variable filters tests
class adc_ctrl_env_var_filters_cfg extends adc_ctrl_env_cfg;

  // If the bit is set then filters for the same channel all have same control bits
  rand bit [ADC_CTRL_NUM_FILTERS-1:0] mirror_controls;

  // Use maximum / minimum value for filter
  rand bit [ADC_CTRL_NUM_FILTERS-1:0] max_val;
  rand bit [ADC_CTRL_NUM_FILTERS-1:0] min_val;
  // Apply max or min to max_v 1 or min_v 0
  rand bit [ADC_CTRL_NUM_FILTERS-1:0] apply_max_v;


  // Constants used in ranges below
  localparam int MAX_VALUE = (2 ** ADC_CTRL_DATA_WIDTH) - 1;
  localparam int THREE_THIRTYSECONDTHS = 3 * (2 ** (ADC_CTRL_DATA_WIDTH - 5));
  localparam int FIVE_THIRTYSECONDTHS = 5 * (2 ** (ADC_CTRL_DATA_WIDTH - 5));
  localparam int ONE_SIXTYFOURTH = 2 ** (ADC_CTRL_DATA_WIDTH - 6);

  `uvm_object_utils_begin(adc_ctrl_env_var_filters_cfg)
    `uvm_field_int(mirror_controls, UVM_DEFAULT | UVM_BIN)
    `uvm_field_int(max_val, UVM_DEFAULT | UVM_BIN)
    `uvm_field_int(min_val, UVM_DEFAULT | UVM_BIN)
    `uvm_field_int(apply_max_v, UVM_DEFAULT | UVM_BIN)
  `uvm_object_utils_end

  `uvm_object_new

  // Modify defaults
  constraint defaults_c {
    // Power / wake up - different values to reset
    soft pwrup_time inside {[3 : 7]};
    soft wakeup_time inside {[4 : 30]};
    // Debouncing sample counts for normal and low power mode
    soft np_sample_cnt inside {[2 : 15]};
    soft lp_sample_cnt inside {[2 : 15]};
  }

  constraint apply_max_v_c {
    // Only either max or min for each filter
    (max_val & min_val) == 0;

    foreach (max_val[filter]) {

      // 1 in 15 are max or min
      max_val[filter] dist {
        1 := 1,
        0 := 29
      };
      min_val[filter] dist {
        1 := 1,
        0 := 29
      };
    }
  }

  constraint filters_values_c {
    solve max_val, min_val, apply_max_v before filter_cfg;
    foreach (filter_cfg[channel]) {
      foreach (filter_cfg[channel][filter]) {
        // Set valid values
        filter_cfg[channel][filter].min_v inside {[0 : MAX_VALUE]};
        filter_cfg[channel][filter].max_v inside {[0 : MAX_VALUE]};
        filter_cfg[channel][filter].max_v >= filter_cfg[channel][filter].min_v;

        // Set first channel to about 1/8 full range so 3/32 to 5/32
        // then make others within 1/64 range of it so there is some overlap
        if (channel == 0) {
          // Channel 0
          // Make this a soft constraint as it can be broken by minimum and maximum values
          // If min_v == full range then so must max_v, if max_v == 0 then so must min_v
          soft (filter_cfg[channel][filter].max_v - filter_cfg[channel][filter].min_v) inside {
                [THREE_THIRTYSECONDTHS:FIVE_THIRTYSECONDTHS]};
          // Set maximum/minimum values
          if (max_val[filter]) {
            if (apply_max_v[filter]) {
              filter_cfg[channel][filter].max_v == MAX_VALUE;
            } else {
              filter_cfg[channel][filter].min_v == MAX_VALUE;
            }
          }
          if (min_val[filter]) {
            if (apply_max_v[filter]) {
              filter_cfg[channel][filter].max_v == 0;
            } else {
              filter_cfg[channel][filter].min_v == 0;
            }
          }
        } else {
          // Other channels within 1/64
          (filter_cfg[channel][filter].min_v - filter_cfg[0][filter].min_v) inside
            {[-ONE_SIXTYFOURTH : ONE_SIXTYFOURTH]};
          (filter_cfg[channel][filter].max_v - filter_cfg[0][filter].max_v) inside
            {[-ONE_SIXTYFOURTH : ONE_SIXTYFOURTH]};
        }
      }
    }
  }

  constraint mirror_controls_c {
    // Usually mirror channel 0 - free one of the filters to do the opposite
    $onehot(~mirror_controls);
  }
  constraint filters_control_c {
    foreach (filter_cfg[channel]) {
      foreach (filter_cfg[channel][filter]) {
        if (mirror_controls[filter]) {
          filter_cfg[channel][filter].cond == filter_cfg[0][filter].cond;
          filter_cfg[channel][filter].en == filter_cfg[0][filter].en;
        }
      }
    }
  }


endclass
