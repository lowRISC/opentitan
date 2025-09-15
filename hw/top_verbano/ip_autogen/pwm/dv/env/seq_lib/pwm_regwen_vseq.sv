// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence attempts to change the configuration registers of the DUT after the `regwen`
// bit has been cleared to protect against further changes.
// The `regwen` bit should be protecting against writes to any field within any of the PWM
// configuration registers.
class pwm_regwen_vseq extends pwm_rand_output_vseq;
  `uvm_object_utils(pwm_regwen_vseq)

  // Constrain the configuration so that the PWM outputs are definitely changing, making
  // any successful configuration changes more likely to be apparent.
  extern constraint rand_chan_c;
  extern constraint pwm_param_c;

  // These functions override those in `pwm_base_vseq`. We just want to ensure that all outputs are
  // changing.
  extern function duty_cycle_t rand_pwm_duty_cycle();
  extern function blink_param_t rand_pwm_blink();

  extern function new (string name="");
  // Override the monitoring in order to run a parallel process that attempts to change the
  // configuration.
  extern virtual task monitor_dut_outputs(bit low_power_mode, uint cycles);
  // Override the DUT shutdown so that we can guarantee a reset afterwards (this should be the only
  // way to re-enable register writing).
  extern virtual task shutdown_dut();
endclass

constraint pwm_regwen_vseq::rand_chan_c {
  rand_chan == {PWM_NUM_CHANNELS{1'b1}};
}

constraint pwm_regwen_vseq::pwm_param_c {
  foreach (pwm_param[ii]) {
    pwm_param[ii].BlinkEn == 1'b1;
    pwm_param[ii].HtbtEn == 1'b0;
  }
}

function duty_cycle_t pwm_regwen_vseq::rand_pwm_duty_cycle();
  duty_cycle_t ret;
  ret.A = 16'h8000;
  ret.B = 16'h0;
  return ret;
endfunction

function blink_param_t pwm_regwen_vseq::rand_pwm_blink();
  blink_param_t blink;
  blink.X = 11;
  blink.Y = 7;
  return blink;
endfunction

function pwm_regwen_vseq::new (string name = "");
  super.new(name);
endfunction

task pwm_regwen_vseq::monitor_dut_outputs(bit low_power_mode, uint cycles);
  bit stop = 1'b0;

  // Start a parallel process that runs throughout the operation, attempting to change the
  // configuration registers.
  fork
    begin
      // Run the DUT test as normal, including any low power testing etc.
      super.monitor_dut_outputs(low_power_mode, cycles);
      stop = 1'b1;
    end
    begin
      // Clear the `regwen` bit so that the configuration cannot any longer be modified.
      `uvm_info(`gfn, "Clearing REGWEN to lock configuration", UVM_MEDIUM)
      ral.regwen.regwen.set(1'b0);
      csr_update(ral.regwen);

      // Attempt to modify the configuration registers.
      while (!stop) begin
        int unsigned idx = $urandom_range(0, PWM_NUM_CHANNELS - 1);
        uvm_reg_data_t val = $urandom();
        randcase
          // The REGWEN itself.
          1: csr_wr(.ptr(ral.regwen), .value(val));
          // Global configuration.
          1: csr_wr(.ptr(ral.cfg), .value(val));
          1: csr_wr(.ptr(ral.pwm_en[0]), .value(val));
          1: csr_wr(.ptr(ral.invert[0]), .value(val));
          // Channel configuration.
          1: csr_wr(.ptr(ral.pwm_param[idx]), .value(val));
          1: csr_wr(.ptr(ral.duty_cycle[idx]), .value(val));
          1: csr_wr(.ptr(ral.blink_param[idx]), .value(val));
        endcase
      end
    end
  join
endtask

task pwm_regwen_vseq::shutdown_dut();
  `uvm_info(`gfn, "Applying reset to clear REGWEN", UVM_MEDIUM)
  apply_reset();
  `uvm_info(`gfn, "Completed reset", UVM_MEDIUM)
endtask
