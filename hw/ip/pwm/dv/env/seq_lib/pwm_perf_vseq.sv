// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// sequence to check operation at min/max bandwidth
class pwm_perf_vseq extends pwm_rand_output_vseq;
  `uvm_object_utils(pwm_perf_vseq)
  `uvm_object_new

  // variables
  rand bit [15:0] rand_dc;
  rand bit [15:0] rand_blink;

  // constraints
  constraint rand_chan_c {
    rand_chan dist {MAX_32:/1, 0:/1};
  }

  constraint rand_invert_c {
    rand_invert dist {MAX_32:/1, 0:/1};
  }

  constraint rand_reg_param_c {
    rand_reg_param.HtbtEn == 1'b1 -> rand_reg_param.BlinkEn == 1'b1;
    rand_reg_param.RsvParam == 0;
    rand_reg_param.PhaseDelay dist {MAX_16:/1, 0:/1};
  }

  constraint duration_cycles_c {
    duration_cycles == {NUM_CYCLES};
  }

  constraint low_power_c {
    low_power dist {1'b1:/1, 1'b0:/1};
  }

  constraint rand_dc_c {
    rand_dc dist {MAX_16:/1, 16'h1:/1, 16'h0:/1};
  }

  constraint rand_blink_c {
    rand_blink dist {MAX_16:/1, 16'h1:/1, 16'h0:/1};
  }

  virtual task body();

    set_reg_en(Enable);
    set_ch_enables(32'h0);
    rand_pwm_cfg_reg();

    for (uint i = 0; i < PWM_NUM_CHANNELS; i++) begin
      set_duty_cycle(i, .A(rand_dc[i]), .B(rand_dc[i]));
      set_blink(i, .A(rand_blink[i]), .B(rand_blink[i]));

      cfg.pwm_param[i].HtbtEn = rand_reg_param.HtbtEn;
      cfg.pwm_param[i].BlinkEn = rand_reg_param.BlinkEn;
      set_param(i, cfg.pwm_param[i]);
    end

    set_ch_invert(rand_invert);
    set_ch_enables(rand_chan);

    low_power_mode(low_power, duration_cycles);

    `uvm_info(`gfn, $sformatf("Runtime: %d", duration_cycles), UVM_HIGH)
    shutdown_dut();

  endtask : body

endclass : pwm_perf_vseq
