// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence randomizes configurations at the output.
class pwm_rand_output_vseq extends pwm_base_vseq;
  `uvm_object_utils(pwm_rand_output_vseq)

  // A parameter used for pwm_param for each channel
  rand param_reg_t rand_reg_param;

  // Enable and invert bits for each channel
  rand bit [PWM_NUM_CHANNELS-1:0] rand_chan;
  rand bit [PWM_NUM_CHANNELS-1:0] rand_invert;

  // If true, this stops the clock in "low power" mode
  rand bit low_power;

  // Model low power mode 10% of the time.
  extern constraint low_power_c;

  extern function new (string name="");
  extern virtual task body();
endclass

constraint pwm_rand_output_vseq::low_power_c {
  low_power dist {1'b1:/1, 1'b0:/9};
}

function pwm_rand_output_vseq::new (string name = "");
  super.new(name);
endfunction

task pwm_rand_output_vseq::body();
  set_ch_enables(32'h0);
  rand_pwm_cfg_reg();

  // Set random dc and params for all channels
  for (uint i = 0; i < PWM_NUM_CHANNELS; i++) begin
    dc_blink_t blink, duty_cycle;

    duty_cycle = rand_pwm_duty_cycle();
    blink = rand_pwm_blink(duty_cycle);

    set_duty_cycle(i, .A(duty_cycle.A), .B(duty_cycle.B));
    set_blink(i, .A(blink.A), .B(blink.B));
    set_param(i, rand_reg_param);
  end

  set_ch_invert(rand_invert);
  set_ch_enables(rand_chan);

  low_power_mode(low_power, NUM_CYCLES);

  shutdown_dut();
endtask
