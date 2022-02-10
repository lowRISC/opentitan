// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
/*
  typedef struct packed {
    bit          BlinkEn;
    bit          HtbtEn;
    bit [13:0]   RsvParam;
    bit [15:0]   PhaseDelay;
  } param_reg_t;

  typedef struct packed {
    bit [15:0]   B;
    bit [15:0]   A;
  } dc_blink_t;
 */ 
class pwm_base_vseq extends cip_base_vseq #(
  .RAL_T              (pwm_reg_block),
  .CFG_T              (pwm_env_cfg),
  .COV_T              (pwm_env_cov),
  .VIRTUAL_SEQUENCER_T(pwm_virtual_sequencer)
);
  `uvm_object_utils(pwm_base_vseq)
  `uvm_object_new

  // enable regs
  // wr1c
  virtual task set_reg_en(pwm_status_e state);
    if (ral.regwen.regwen.get_mirrored_value() != state) begin
      ral.regwen.regwen.set(1'b1);
      csr_update(.csr(ral.regwen), .en_shadow_wr(1'b1));
    end
  endtask

  virtual task set_cfg_reg(cfg_reg_t cfg_reg);
    ral.cfg.clk_div.set(cfg_reg.ClkDiv);
    ral.cfg.dc_resn.set(cfg_reg.DcResn);
    ral.cfg.cntr_en.set(cfg_reg.CntrEn);
    csr_update(ral.cfg);
  endtask

  virtual task set_ch_enables(bit [PWM_NUM_CHANNELS-1:0] enables);
    bit [31:0] reg_val = 32'h0;
    reg_val = enables;
    csr_wr(.ptr(ral.pwm_en[0]), .value(reg_val));
    // also activate monitor
    foreach (enables[ii]) begin
      cfg.m_pwm_monitor_cfg[ii].active = enables[ii];
    end
  endtask


  virtual task set_duty_cycle(bit [$bits(PWM_NUM_CHANNELS)-1:0] channel, dc_blink_t value);
    ral.duty_cycle[channel].set({value.B,value.A});
    csr_update(ral.duty_cycle[channel]);
  endtask

  //virtual task set_polarity(bit [$bits(PWM_NUM_CHANNELS)-1:0] channel, bit [$bits(PWM_NUM_CHANNELS)-1:0] value);
  virtual task set_polarity(bit [$bits(PWM_NUM_CHANNELS)-1:0] channel, value);
    ral.invert[channel].set(value);
    csr_update(ral.invert[channel]);
    // also set invert in the monitor
    cfg.m_pwm_monitor_cfg[channel].invert = value;
  endtask

  virtual task set_blink(bit [$bits(PWM_NUM_CHANNELS)-1:0] channel, dc_blink_t value);
    ral.blink_param[channel].set(value);
    csr_update(ral.blink_param[channel]);
  endtask // set_blink

  virtual task set_param(bit [$bits(PWM_NUM_CHANNELS)-1:0] channel, param_reg_t value);
    ral.pwm_param[channel].set(value);
    csr_update(ral.pwm_param[channel]);
  endtask // set_param


  // override apply_reset to handle reset for bus and core domain
  virtual task apply_reset(string kind = "HARD");
    fork
      if (kind == "HARD" || kind == "TL_IF") begin
        super.apply_reset("HARD");
      end
      if (kind == "HARD" || kind == "CORE_IF") begin
        cfg.clk_rst_core_vif.apply_reset();
      end
    join
  endtask : apply_reset

   virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.clk_rst_core_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(cfg.clk_rst_core_vif.clk_period_ps);
    cfg.clk_rst_core_vif.drive_rst_pin(1);
  endtask

  virtual task shutdown_dut();
    // shutdown dut to make last item finish gracefully
    `uvm_info(`gfn, $sformatf("disabling channel"), UVM_HIGH)
    set_ch_enables(6'b0);
  endtask

  function void set_basics(input int dcresn, int clkdiv, int cntren);
    cfg.pwm_cfg.DcResn       = dcresn;
    cfg.pwm_cfg.ClkDiv       = clkdiv;
    cfg.pwm_cfg.CntrEn       = cntren;
  endfunction

  function void set_blk_htbt(input int dca, int dcb, int blka, int blkb, bit blken, bit htbten);
    cfg.duty_cycle[0].A      = dca;
    cfg.duty_cycle[0].B      = dcb;
    cfg.blink[0].A           = blka;
    cfg.blink[0].B           = blkb;
    cfg.pwm_param[0].BlinkEn = blken;
    cfg.pwm_param[0].HtbtEn  = htbten;
  endfunction

endclass : pwm_base_vseq
