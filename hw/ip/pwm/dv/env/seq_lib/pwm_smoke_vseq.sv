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
    int rd_data;
    int phdel [$];
    int i = 0;

    phdel = '{0, 12, 32000};
    //make sure write to regs are enabled
    set_reg_en(Enable);
    `uvm_info(`gfn, "Starting with blink", UVM_HIGH)
    // disable channel 0
    set_ch_enables(32'h0);
    //setup general config
    //set_basics(10, 1, 1);
    set_basics(15, 1, 1);
    set_cfg_reg(cfg.pwm_cfg);
//
    repeat (5) begin
      int tmp;
      tmp = $urandom_range(50000, 10000);
      `uvm_info(`gfn, $sformatf("urandom = %d", tmp), UVM_HIGH)
    //  cfg.duty_cycle[0].A      = 50000 + 100*i;  //50000
    //  cfg.duty_cycle[0].A      = 34456 + i;  //50000
      cfg.duty_cycle[0].A        = tmp; //50000
    //  cfg.duty_cycle[0].A      = tmp;  //50000
     // cfg.duty_cycle[0].B      = 2500;  //$urandom_range(500, 2500);   //2500
      //
   //   cfg.blink[0].A           = 6;
   //   cfg.blink[0].B           = 2;
   //   cfg.pwm_param[0].BlinkEn = 1'b0;
   //   cfg.pwm_param[0].HtbtEn  = 1'b0;

      set_duty_cycle(0, cfg.duty_cycle[0]);
   //   set_blink(0, cfg.blink[0]);
   //   set_param(0, cfg.pwm_param[0]);

      set_ch_enables(32'h1);
      // add some run time so we get some pulses
      cfg.clk_rst_vif.wait_clks(200000);
      i++;
    end
    `uvm_info(`gfn, "Ending Pulse", UVM_HIGH)
    `uvm_info(`gfn, "Calling shutdown", UVM_HIGH) 
    shutdown_dut();
  endtask
//
/*
    //set_blinking(13000, 6500, 6, 2, 1'b1);
    set_blk_htbt(23000, 2500, 6, 2, 1'b1, 1'b0);
    set_duty_cycle(0, cfg.duty_cycle[0]);
    set_blink(0, cfg.blink[0]);
    set_param(0, cfg.pwm_param[0]);
    // enable channel 0
    set_ch_enables(32'h1);
    // add some run time so we get some pulses
    cfg.clk_rst_vif.wait_clks(100000);
    `uvm_info(`gfn, "Ending Blink", UVM_HIGH)
    `uvm_info(`gfn, "Starting Pulse", UVM_HIGH)
    // disable channel 0
    set_ch_enables(32'h0);
    cfg.pwm_param[0].BlinkEn  = 1'b0;   // Resetting BlinkEn
    set_param(0, cfg.pwm_param[0]);
    // enable channel 0
    set_ch_enables(32'h1);
    cfg.clk_rst_vif.wait_clks(50000);
    `uvm_info(`gfn, "Ending Pulse", UVM_HIGH)
    
    `uvm_info(`gfn, "Start polarity", UVM_HIGH)
    // disable channel 0
    set_ch_enables(32'h0);
    cfg.invert[0] = 1'b1;
    set_polarity(0, cfg.invert[0]);
    set_ch_enables(32'h1);
    csr_rd(.ptr(ral.invert[0].invert[0]), .value(rd_data));
    `uvm_info(`gfn, $sformatf("read invert reg = %0b", rd_data), UVM_HIGH) 
    cfg.clk_rst_vif.wait_clks(50000);
    `uvm_info(`gfn, "End polarity", UVM_HIGH)
*/    
/*
    `uvm_info(`gfn, "Starting HeartBeat", UVM_HIGH)
    `uvm_info(`gfn, "Setting registers", UVM_HIGH)
  //  set_blk_htbt(23000, 2500, 6, 2, 1'b1, 1'b1);
    cfg.duty_cycle[0].A      = 23000;
    cfg.duty_cycle[0].B      = 2500;
    cfg.blink[0].A           = 6;
    cfg.blink[0].B           = 2;
    cfg.pwm_param[0].BlinkEn = 1'b1;
    cfg.pwm_param[0].HtbtEn  = 1'b1;
    set_duty_cycle(0, cfg.duty_cycle[0]);
    set_blink(0, cfg.blink[0]);
    set_param(0, cfg.pwm_param[0]);
    // enable channel 0
    set_ch_enables(32'h1);
 /* 
  // add some run time so we get some pulses
    cfg.clk_rst_vif.wait_clks(50000);
    `uvm_info(`gfn, "Ending Heartbeat", UVM_HIGH)
*/    

endclass : pwm_smoke_vseq

// polarity test vseq: accessing a major datapath within the pwm
class pwm_polarity_vseq extends pwm_base_vseq;
  `uvm_object_utils(pwm_polarity_vseq)
  `uvm_object_new

    // variables

    virtual task pre_start();
      super.pre_start();
    endtask // pre_start

  virtual task body();
    int rd_data;
    //make sure write to regs are enabled
    set_reg_en(Enable);
    ral.cfg.reset("HARD");
    `uvm_info(`gfn, "Setup polarity", UVM_HIGH)
    // disable channel 0
    set_ch_enables(32'h0);
    //setup general config
    cfg.pwm_cfg.DcResn       = 10;
    cfg.pwm_cfg.ClkDiv       = 1;
    cfg.pwm_cfg.CntrEn       = 1;

    set_cfg_reg(cfg.pwm_cfg);

    cfg.duty_cycle[0].A      = 13000;
    cfg.duty_cycle[0].B      = 6500;
    cfg.blink[0].A           = 6;
    cfg.blink[0].B           = 2;
    cfg.pwm_param[0].BlinkEn = 0;

    set_duty_cycle(0, cfg.duty_cycle[0]);
  //  set_blink(0, cfg.blink[0]);
    set_param(0, cfg.pwm_param[0]);

    // invert
    `uvm_info(`gfn, "Start polarity", UVM_HIGH)
    set_polarity(0, 1'b1);
  //  csr_wr(.ptr(ral.invert[0].invert[0]), .value(1'b1));
  //  csr_update(ral.invert[0]);
//    read_and_check_all_csrs(ral);
    // enable channel 0
    csr_rd(.ptr(ral.invert[0].invert[0]), .value(rd_data));
    `uvm_info(`gfn, $sformatf("read invert reg = %0b", rd_data), UVM_HIGH) 
    set_ch_enables(32'h1);
    cfg.clk_rst_vif.wait_clks(150000);
    `uvm_info(`gfn, "Calling shutdown", UVM_HIGH) 
    shutdown_dut();
  endtask

/*
  virtual task body();
    int rd_data;
    //make sure write to regs are enabled
    set_reg_en(Enable);
    // invert
    `uvm_info(`gfn, "Start polarity", UVM_HIGH)
    // disable channel 0
    set_ch_enables(32'h0);
    set_basics(10, 1, 1);
    set_cfg_reg(cfg.pwm_cfg);
    set_polarity(0, 1'b1);
 //   csr_wr(.ptr(ral.invert[0].invert[0]), .value(1'b1));
 //   csr_update(ral.invert[0]);
//    csr_rd(.ptr(ral.invert[0].invert[0]), .value(rd_data));
//    `uvm_info(`gfn, $sformatf("read invert reg = %0b", rd_data), UVM_HIGH) 
    // enable channel 0
    set_ch_enables(32'h1);
    cfg.clk_rst_vif.wait_clks(100000);
    `uvm_info(`gfn, "Calling shutdown", UVM_HIGH) 
    shutdown_dut();
  endtask
*/  
endclass: pwm_polarity_vseq

  class pwm_heartbeat_vseq extends pwm_base_vseq;
  `uvm_object_utils(pwm_heartbeat_vseq)
  `uvm_object_new


    // variables

    virtual task pre_start();
      super.pre_start();
    endtask // pre_start


  virtual task body();
    int rd_data;
    set_reg_en(Enable);
   
// Heartbeat does not work

    `uvm_info(`gfn, "Starting HeartBeat", UVM_HIGH)
//
        `uvm_info(`gfn, "Starting HeartBeat", UVM_HIGH)
    // disable channel 0
    set_ch_enables(32'h0);

    `uvm_info(`gfn, "Setting registers", UVM_HIGH)
    set_blk_htbt(23000, 2500, 6, 2, 1'b1, 1'b1);

    set_duty_cycle(0, cfg.duty_cycle[0]);
    set_blink(0, cfg.blink[0]);
    set_param(0, cfg.pwm_param[0]);
//
/*
    // disable channel 0
    set_ch_enables(32'h0);
    `uvm_info(`gfn, "Setting registers", UVM_HIGH)
    cfg.duty_cycle[0].A      = 3;
    cfg.duty_cycle[0].B      = 21;
    cfg.blink[0].A     = 1;
    cfg.blink[0].B     = 4;
    cfg.pwm_param[0].BlinkEn = 1;
    
    cfg.pwm_param[0].HtbtEn = 1;

    csr_wr(.ptr(ral.blink_param[0].x), .value(1));
    csr_wr(.ptr(ral.blink_param[0].y), .value(4));
    csr_update(ral.blink_param[0]);
    csr_rd(.ptr(ral.blink_param[0].x), .value(rd_data));
    `uvm_info(`gfn, $sformatf("blink_param_x = %0d", rd_data), UVM_HIGH)
    csr_rd(.ptr(ral.blink_param[0].y), .value(rd_data));
    `uvm_info(`gfn, $sformatf("blink_param_y = %0d", rd_data), UVM_HIGH)
    set_duty_cycle(0, cfg.duty_cycle[0]);
    set_param(0, cfg.pwm_param[0]);
*/
    // enable channel 0
    set_ch_enables(32'h1);

    // add some run time so we get some pulses
    cfg.clk_rst_vif.wait_clks(50000);
  
    `uvm_info(`gfn, "Calling shutdown", UVM_HIGH) 
    shutdown_dut();
  endtask

endclass : pwm_heartbeat_vseq


