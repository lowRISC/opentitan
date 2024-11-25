// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Smoke test vseq: accessing a major datapath within the pwm
class pwm_smoke_vseq extends pwm_base_vseq;
  `uvm_object_utils(pwm_smoke_vseq)

  extern function new (string name="");
  extern virtual task body();
endclass : pwm_smoke_vseq

function pwm_smoke_vseq::new (string name = "");
  super.new(name);
endfunction

task pwm_smoke_vseq::body();
  param_reg_t pwm_param;
  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(pwm_param, pwm_param.BlinkEn == 1;)

  // disable channel 0
  set_ch_enables(32'h0);
  // set up general config
  set_cfg_reg(10, 1, 1);

  set_duty_cycle(.channel(0), .A(16'hC000), .B(16'h4000));
  set_blink(.channel(0), .A(0), .B(0));
  set_param(0, pwm_param);

  // enable channel 0
  set_ch_enables(32'h1);

  // add some run time so we get some pulses
  cfg.clk_rst_vif.wait_clks(50000);
  shutdown_dut();
endtask
