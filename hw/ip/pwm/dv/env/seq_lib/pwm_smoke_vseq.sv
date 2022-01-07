// Copyright lowRISC contributors.
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
    //make sure write to regs are enabled
    set_reg_en(Enable);

    // disable channel 0
    set_ch_enables(32'h0);
    //setup general config
    cfg.pwm_cfg.DcResn       = 10;
    cfg.pwm_cfg.ClkDiv       = 1;
    cfg.pwm_cfg.CntrEn       = 1;

    set_cfg_reg(cfg.pwm_cfg);

    cfg.duty_cycle[0].A      = 13000;
    cfg.duty_cycle[0].B      = 6500;
    cfg.blink[0].A           = 0;
    cfg.blink[0].B           = 0;
    cfg.pwm_param[0].BlinkEn = 1;


    set_duty_cycle(0, cfg.duty_cycle[0]);
    set_blink(0, cfg.blink[0]);
    set_param(0, cfg.pwm_param[0]);

    // enable channel 0
    set_ch_enables(32'h1);

    // add some run time so we get some pulses
    cfg.clk_rst_vif.wait_clks(50000);
    shutdown_dut();
  endtask

endclass : pwm_smoke_vseq
