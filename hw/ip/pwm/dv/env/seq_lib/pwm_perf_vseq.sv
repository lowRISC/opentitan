// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// sequence to check operation at min/max bandwidth
class pwm_perf_vseq extends pwm_rand_output_vseq;
  `uvm_object_utils(pwm_perf_vseq)

  // The duty cycle used for all channels
  rand bit [15:0]  rand_dc;

  // The blink threshold used for all channels
  rand bit [15:0]  rand_blink;

  // A param_reg_t value to configure each channel
  rand param_reg_t pwm_param[PWM_NUM_CHANNELS];

  // Either enable all channels or none of them. Similarly for inverting channels.
  extern constraint rand_chan_c;
  extern constraint rand_invert_c;

  // Enable "low power mode" half of the time (overriding the constraint with the same name in
  // pwm_rand_output_vseq that uses low power mode less often)
  extern constraint low_power_c;

  // Constrain phase delay to be minimal or maximal
  extern constraint phase_delay_c;

  // The duty cycle and the threshold for the heartbeat blink counter should be minimal or maximal,
  // correspoding to both counters being minimal or both counters being maximal.
  extern constraint rand_dc_c;
  extern constraint rand_blink_c;

  extern function new (string name="");
  extern virtual task body();
endclass

constraint pwm_perf_vseq::rand_chan_c {
  rand_chan dist {MAX_32 :/ 1, 0 :/ 1};
}

constraint pwm_perf_vseq::rand_invert_c {
  rand_invert dist {MAX_32 :/ 1, 0 :/ 1};
}

constraint pwm_perf_vseq::low_power_c {
  low_power dist {1'b1 :/ 1, 1'b0 :/ 1};
}

constraint pwm_perf_vseq::phase_delay_c {
  rand_reg_param.PhaseDelay dist {MAX_16 :/ 1, 0 :/ 1};
}

constraint pwm_perf_vseq::rand_dc_c {
  rand_dc dist {MAX_16 :/ 1, 16'h0 :/ 1};
}

constraint pwm_perf_vseq::rand_blink_c {
  rand_blink dist {MAX_16 :/ 1, 16'h0 :/ 1};
}

function pwm_perf_vseq::new (string name = "");
  super.new(name);
endfunction

task pwm_perf_vseq::body();
  set_ch_enables(32'h0);
  rand_pwm_cfg_reg();

  for (uint i = 0; i < PWM_NUM_CHANNELS; i++) begin
    set_duty_cycle(i, .A(rand_dc), .B(rand_dc));
    set_blink(i, .A(rand_blink), .B(rand_blink));

    pwm_param[i].HtbtEn = rand_reg_param.HtbtEn;
    pwm_param[i].BlinkEn = rand_reg_param.BlinkEn;
    set_param(i, pwm_param[i]);
  end

  set_ch_invert(rand_invert);
  set_ch_enables(rand_chan);

  low_power_mode(low_power, NUM_CYCLES);

  shutdown_dut();

endtask : body
