// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_base_vseq extends cip_base_vseq #(
  .RAL_T              (pwm_reg_block),
  .CFG_T              (pwm_env_cfg),
  .COV_T              (pwm_env_cov),
  .VIRTUAL_SEQUENCER_T(pwm_virtual_sequencer)
);
  `uvm_object_utils(pwm_base_vseq)
  `uvm_object_new

  rand uint duration_cycles;

  constraint duration_cycles_c {
    duration_cycles == {NUM_CYCLES};
  }

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
    foreach(cfg.m_pwm_monitor_cfg[i]) begin
      cfg.m_pwm_monitor_cfg[i].resolution = cfg_reg.DcResn;
    end
  endtask

  virtual task automatic rand_pwm_cfg_reg();
    cfg.pwm_cfg.ClkDiv = $urandom_range(0, MAX_CLK_DIV);
    cfg.pwm_cfg.DcResn = $urandom_range(4'h0, 4'hE);
    cfg.pwm_cfg.CntrEn = 1;
    set_cfg_reg(cfg.pwm_cfg);
  endtask

  virtual task set_ch_invert(bit [PWM_NUM_CHANNELS-1:0] enables);
    csr_wr(.ptr(ral.invert[0]), .value(enables));
    foreach (enables[ii]) begin
      cfg.m_pwm_monitor_cfg[ii].invert = enables[ii];
    end
  endtask

  virtual task set_ch_enables(bit [PWM_NUM_CHANNELS-1:0] enables);
    csr_wr(.ptr(ral.pwm_en[0]), .value(enables));
    foreach (enables[ii]) begin
      cfg.m_pwm_monitor_cfg[ii].active = enables[ii];
    end
  endtask

  virtual task set_duty_cycle(bit [$bits(PWM_NUM_CHANNELS)-1:0] channel, dc_blink_t value);
    ral.duty_cycle[channel].set({value.B,value.A});
    csr_update(ral.duty_cycle[channel]);
  endtask

  virtual task automatic rand_pwm_duty_cycle(bit [$bits(PWM_NUM_CHANNELS)-1:0] channel);
    cfg.duty_cycle[channel].A = $urandom_range(16'h1, MAX_16);
    cfg.duty_cycle[channel].B = $urandom_range(16'h1, MAX_16);
    set_duty_cycle(channel, cfg.duty_cycle[channel]);
  endtask

  virtual task set_blink(bit [$bits(PWM_NUM_CHANNELS)-1:0] channel, dc_blink_t value);
    ral.blink_param[channel].set(value);
    csr_update(ral.blink_param[channel]);
  endtask // set_blink

  virtual task automatic rand_pwm_blink(bit [$bits(PWM_NUM_CHANNELS)-1:0] channel);
    cfg.blink[channel].A = $urandom_range(16'h1, MAX_16);
    cfg.blink[channel].B = $urandom_range(16'h1, MAX_16);
    set_blink(channel, cfg.blink[channel]);
  endtask

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

  virtual task low_power_mode(bit enable, uint cycles);
    if (enable) begin
      `uvm_info(`gfn, "Running in low power mode...", UVM_HIGH)
      cfg.clk_rst_vif.wait_clks(cycles/2);
      // in the middle of test turn off tl_ul clk to observe that
      // the output does not change
      cfg.clk_rst_vif.stop_clk();
      // use core clk to determine when to turn tl_ul clk back on
      cfg.clk_rst_core_vif.wait_clks(1);
      cfg.clk_rst_vif.start_clk();
      cfg.clk_rst_vif.wait_clks(cycles/2);
    end else begin
      cfg.clk_rst_vif.wait_clks(cycles);
    end
  endtask

  virtual task shutdown_dut();
    // shutdown dut to make last item finish gracefully
    `uvm_info(`gfn, $sformatf("disabling channel"), UVM_HIGH)
    set_ch_enables(32'h0);
    dut_shutdown();
  endtask
endclass : pwm_base_vseq
