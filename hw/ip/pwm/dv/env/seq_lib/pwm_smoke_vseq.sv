// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq: accessing a major datapath within the pwm
class pwm_smoke_vseq extends pwm_base_vseq;
  `uvm_object_utils(pwm_smoke_vseq)
  `uvm_object_new


    // variables

    virtual task pre_start();
      super.pre_start();
    endtask // pre_start


  virtual task body();
    dc_blink_t duty_cycle;

    //make sure write to regs are enabled
    set_reg_en(Enable);

    // disable channel 0
    set_ch_enables(32'h0);
    //setup general config
    set_cfg_reg(10, 1, 1);

    duty_cycle.A             = 13000;
    duty_cycle.B             = 6500;
    cfg.blink[0].A           = 0;
    cfg.blink[0].B           = 0;
    cfg.pwm_param[0].BlinkEn = 1;

    set_duty_cycle(0, duty_cycle);
    set_blink(0, cfg.blink[0]);
    set_param(0, cfg.pwm_param[0]);

    // enable channel 0
    set_ch_enables(32'h1);

    // add some run time so we get some pulses
    cfg.clk_rst_vif.wait_clks(50000);
    shutdown_dut();
  endtask

endclass : pwm_smoke_vseq
