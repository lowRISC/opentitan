// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sysrst_ctrl_in_irq_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sysrst_ctrl_in_irq_vseq)

  `uvm_object_new

  // Parameters for generation of input pad signals. Using generate_inputs task.
  // The generate task uses a 1us time step and will generate the required 'valid' inputs and
  // create random glitches on all other inputs.
  localparam uint AON_CLK_PERIOD_US = 5;
  // The number of cycles for the threshold (Talso backdoor written to SW).
  localparam uint THRESHOLD_CYCLES = 16;
  // A number of extra cycles to hold the signal past the threshold
  // to ensure a trigger.
  localparam uint EXTRA_CYCLES = 5;
  // A number of cycles before the end of the threshold period to remove any
  // randomly generated glitchy signals (ensures they will not become valid inputs!)
  localparam uint END_GLITCH_CYCLES = 2;
  // The number of time steps to generate signals for.
  localparam uint GEN_NUM_SAMPLES = (THRESHOLD_CYCLES + EXTRA_CYCLES) * AON_CLK_PERIOD_US;
  // The maximum sample where the glitched signal can be written.
  localparam uint MAX_GLITCH_SAMPLE = (THRESHOLD_CYCLES - END_GLITCH_CYCLES) * AON_CLK_PERIOD_US;

  localparam uint NUM_COMBINATIONS = 4;
  localparam uint NUM_INPUTS = 7;

  // Define combinations of inputs to generate.
  localparam bit [NUM_INPUTS-1:0] INITIAL_VALUE = 'b0011111;
  localparam bit [NUM_INPUTS-1:0] COMBO_KEY0_KEY1_VALUE = 'b0000011;
  localparam bit [NUM_INPUTS-1:0] COMBO_KEY0_KEY2_VALUE = 'b0000101;
  localparam bit [NUM_INPUTS-1:0] COMBO_KEY1_KEY2_VALUE = 'b0000110;
  localparam bit [NUM_INPUTS-1:0] COMBO_PWRB_ACPRES_VALUE = 'b0011000;

  virtual function void set_pad(input int index, input bit pad_value);
    case (index)
      0: cfg.sysrst_ctrl_vif.drive_pin(0, pad_value);  //IOB3 KEY0
      1: cfg.sysrst_ctrl_vif.drive_pin(1, pad_value);  //IOB6 KEY1
      2: cfg.sysrst_ctrl_vif.drive_pin(2, pad_value);  //IOB8 KEY2
      3: cfg.pwrb_in_vif.drive_pin(0, pad_value);  //IOR13 PWRB
      4: cfg.sysrst_ctrl_vif.drive_pin(4, pad_value);  //IOC7 ACPRES
      5: cfg.ec_rst_vif.drive_pin(0, pad_value);  //IOR8 EC_RST
      default: cfg.flash_wp_vif.drive_pin(0, pad_value);  //IOR9 FLASHWP (case 6 or greater)
    endcase
  endfunction

  virtual function void set_pads(bit [NUM_INPUTS-1:0] pad_values);
    foreach (pad_values[i]) begin
      set_pad(i, pad_values[i]);
    end
  endfunction

  virtual task generate_inputs(input bit [NUM_INPUTS-1:0] combo);
    int next_transition[NUM_INPUTS] = '{default: 0};
    bit [NUM_INPUTS-1:0] current_values = INITIAL_VALUE;
    bit [NUM_INPUTS-1:0] combo_done = '0;
    for (int sample = 0; sample < GEN_NUM_SAMPLES; sample ++) begin
      for (int index = 0; index < NUM_INPUTS; index++) begin
        if (combo[index] == 1) begin
          if (combo_done[index] == 0) begin
            set_pad(index, ~INITIAL_VALUE[index]);
            combo_done[index] = 1;
          end
        end else begin
          if (sample >= MAX_GLITCH_SAMPLE) begin
            set_pad(index, INITIAL_VALUE[index]);
          end else begin
            if (next_transition[index] == sample) begin
              if (sample == 0) begin
                next_transition[index] = $urandom_range(1, GEN_NUM_SAMPLES);
              end else begin
                set_pad(index, ~current_values[index]);
                current_values[index]  = ~current_values[index];
                next_transition[index] = sample + $urandom_range(1, GEN_NUM_SAMPLES);
              end
            end
          end
        end
      end
      #1us;
    end
    set_pads(INITIAL_VALUE);
    #1;
  endtask

  virtual task do_combo_tests();
    bit [NUM_INPUTS-1:0] combo;
    for (int i = 0; i < NUM_COMBINATIONS; i++) begin
      wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest);
      wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi);
      #20us;
      case (i)
        0: combo = COMBO_KEY0_KEY1_VALUE;
        1: combo = COMBO_KEY0_KEY2_VALUE;
        2: combo = COMBO_KEY1_KEY2_VALUE;
        3: combo = COMBO_PWRB_ACPRES_VALUE;
        default: combo = 'b0000000;
      endcase
      generate_inputs(combo);
    end
  endtask

  virtual task do_input_tests();
    for (int i = 0; i < NUM_INPUTS; i++) begin
      wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest);
      wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi);
      #20us;
      generate_inputs(1 << i);
    end
  endtask

  virtual task body();
    bit [7:0] threshold_backdoor[1] = '{default: THRESHOLD_CYCLES[7:0]};
    super.body();
    sw_symbol_backdoor_overwrite("kThreshold", threshold_backdoor);
    set_pads(INITIAL_VALUE);
    do_input_tests();
    do_combo_tests();
  endtask

endclass
