// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests operation with PWM outputs having a specific phase relationship, starting all channels
// either synchronously or in a staggered fashion.
class pwm_phase_vseq extends pwm_rand_output_vseq;
  `uvm_object_utils(pwm_phase_vseq)

  // Decide whether to start all channels synchronously, as opposed to staggered.
  rand bit sync_start;

  // Constrain the configuration so that all PWM outputs are enabled and have a defined phase
  // relationship. The other configuration we allow to be randomized.
  extern constraint rand_chan_c;
  extern constraint rand_invert_c;
  extern constraint pwm_param_c;

  extern function new (string name="");
  extern virtual task body();
endclass

// All channels shall be enabled.
constraint pwm_phase_vseq::rand_chan_c {
  rand_chan == {PWM_NUM_CHANNELS{1'b1}};
}

// Higher-numbered channels are the phase inversion of the lower ones.
constraint pwm_phase_vseq::rand_invert_c {
  rand_invert == { {(PWM_NUM_CHANNELS/2){1'b1}},    // Complementary signals.
                   {(PWM_NUM_CHANNELS/2){1'b0}} };  // Base signals.
}

// We typically have 6 outputs, so set them up as two triples, with the signals in each triple
// being at 120-degree intervals.
constraint pwm_phase_vseq::pwm_param_c {
  foreach (pwm_param[ii]) {
    pwm_param[ii].BlinkEn == 1'b1;
    pwm_param[ii].HtbtEn == 1'b0;
    pwm_param[ii].PhaseDelay == ((ii % 3) << 16) / 3;
  }
}

function pwm_phase_vseq::new (string name = "");
  super.new(name);
endfunction

// TODO: We should perhaps move some the set up code into a base task which may be overridden
// without replacing the entire `body`.
task pwm_phase_vseq::body();
  // Blink mode parameters to be used for all channels.
  int unsigned blink_pulses_X = $urandom_range(7,  15);
  int unsigned blink_pulses_Y = $urandom_range(11, 23);
  set_ch_enables(32'h0);

  // Set random dc and params for all channels
  for (uint i = 0; i < PWM_NUM_CHANNELS; i++) begin
    set_duty_cycle(i, .A(16'h4000), .B(16'hC000));
    set_blink(i, .X(blink_pulses_X), .Y(blink_pulses_Y));
    set_param(i, pwm_param[i]);
  end
  set_ch_invert(rand_invert);

  // Start the phase counter.
  rand_pwm_cfg_reg();

  `uvm_info(`gfn, $sformatf("Starting phased channels at the same time %0d", sync_start),
            UVM_MEDIUM)

  if (sync_start) begin
    // Enable all of the channels at the same time; the specification requires synchronized
    // starting of multiple channels. All duty cycle changes on all channels should occur
    // simultaneously, except for the delays caused by the phase delays.
    set_ch_enables(rand_chan);
  end else begin
    // Start them in a staggered fashion. Nonetheless they should still have the same phase
    // relationship, but because they've started at different times, they will not necessarily
    // modify their duty cycles on the same pulse cycles.
    uvm_reg_data_t en = rand_chan;
    uvm_reg_data_t set_en = 0;
    while (en) begin
      // Lift the MSB from the chosen set of enables, and set it in the register configuration.
      set_en |= (en & ~(en - 1));
      set_ch_enables(set_en);
      // Proceed to the next enable.
      en &= ~set_en;
    end
  end

  monitor_dut_outputs(low_power, NUM_CYCLES);

  shutdown_dut();
endtask
