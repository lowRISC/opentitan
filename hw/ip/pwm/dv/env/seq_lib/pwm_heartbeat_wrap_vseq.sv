// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A version of pwm_rand_output_vseq that is constrained to ensure that it does heartbeats and wraps
// (to 16 bits) reasonably quickly.
class pwm_heartbeat_wrap_vseq extends pwm_rand_output_vseq;
  `uvm_object_utils(pwm_heartbeat_wrap_vseq)

  // Enable heartbeat (since we're trying to make it wrap, so it definitely needs to be enabled)
  extern constraint with_heartbeat_c;

  extern function new (string name="");

  // This overrides a function from pwm_base_vseq. We want to choose a "maximal" duty cycle, where A
  // and B are near the endpoints of the 16 bit data type (to make it likely that the increment will
  // wrap).
  extern function dc_blink_t rand_pwm_duty_cycle();

  // This overrides a function from pwm_base_vseq. We want to choose a large value for blink.B. This
  // is used as the increment for the duty cycle in heartbeat mode and we want to get through the 16
  // bit range quickly.
  extern function dc_blink_t rand_pwm_blink(dc_blink_t duty_cycle);
endclass

constraint pwm_heartbeat_wrap_vseq::with_heartbeat_c {
  rand_reg_param.HtbtEn == 1'b1;
}

function pwm_heartbeat_wrap_vseq::new (string name);
  super.new(name);
endfunction

function dc_blink_t pwm_heartbeat_wrap_vseq::rand_pwm_duty_cycle();
  dc_blink_t ret;
  int low_delta = $urandom_range(0, 100), high_delta = $urandom_range(0, 100);
  bit a_lt_b = $urandom_range(0, 1);

  ret.A = a_lt_b ? low_delta : MAX_16 - high_delta;
  ret.B = a_lt_b ? MAX_16 - high_delta : low_delta;
  return ret;
endfunction

function dc_blink_t pwm_heartbeat_wrap_vseq::rand_pwm_blink(dc_blink_t duty_cycle);
  dc_blink_t ret = super.rand_pwm_blink(duty_cycle);

  // Make sure that ret.B is large
  ret.B |= 16'hf000;
  return ret;
endfunction
