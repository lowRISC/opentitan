// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence randomizes configurations at the output.
class pwm_rand_output_vseq extends pwm_base_vseq;
  `uvm_object_utils(pwm_rand_output_vseq)
  `uvm_object_new

  // variables
  rand param_reg_t rand_reg_param;
  rand bit [PWM_NUM_CHANNELS-1:0] rand_chan;
  rand bit [PWM_NUM_CHANNELS-1:0] rand_invert;
  rand bit low_power;

  // constraints
  constraint rand_reg_param_c {
   rand_reg_param.HtbtEn == 1'b1 -> rand_reg_param.BlinkEn == 1'b1;
   rand_reg_param.RsvParam == 0;
   rand_reg_param.PhaseDelay inside {[0:MAX_16]};
  }

  constraint low_power_c {
    // 1 in 10, in low power mode
    low_power dist {1'b1:/1, 1'b0:/9};
  }

  virtual task body();

    set_reg_en(Enable);
    set_ch_enables(32'h0);

    rand_pwm_cfg_reg();

    // set random dc and params for all channels
    for (uint i = 0; i < PWM_NUM_CHANNELS; i++) begin
      dc_blink_t duty_cycle = rand_pwm_duty_cycle();
      param_reg_t pwm_param;

      pwm_param.PhaseDelay = (rand_reg_param.PhaseDelay * (2**(-16)));
      pwm_param.HtbtEn = rand_reg_param.HtbtEn;
      pwm_param.BlinkEn = rand_reg_param.BlinkEn;

      set_duty_cycle(i, .A(duty_cycle.A), .B(duty_cycle.B));
      rand_pwm_blink(i);

      // phase delay of the PWM rising edge, in units of 2^(-16) PWM cycles
      set_param(i, pwm_param);
    end

    set_ch_invert(rand_invert);
    set_ch_enables(rand_chan);

    low_power_mode(low_power, NUM_CYCLES);

    shutdown_dut();
    set_reg_en(Disable);

  endtask : body

endclass : pwm_rand_output_vseq
