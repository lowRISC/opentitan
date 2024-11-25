// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_base_vseq extends cip_base_vseq #(
  .RAL_T              (pwm_reg_block),
  .CFG_T              (pwm_env_cfg),
  .COV_T              (pwm_env_cov),
  .VIRTUAL_SEQUENCER_T(pwm_virtual_sequencer)
);
  `uvm_object_utils(pwm_base_vseq)
  extern function new (string name="");

  // Tasks overridden from dv_base_vseq
  extern task apply_reset(string kind = "HARD");
  extern task apply_resets_concurrently(int reset_duration_ps = 0);

  // Set the CFG register with the given ClkDiv, DcResn, CntrEn with a CSR write
  extern task set_cfg_reg(bit [26:0] ClkDiv, bit [3:0] DcResn, bit CntrEn);

  // Pick a random value for the CFG register with cntr_en=1.
  extern task rand_pwm_cfg_reg();

  // Use a CSR write to set the INVERT bits as requested.
  extern task set_ch_invert(bit [PWM_NUM_CHANNELS-1:0] enables);

  // Use a CSR write to set the PWM_EN bits as requested.
  extern task set_ch_enables(bit [PWM_NUM_CHANNELS-1:0] enables);

  // Use a CSR write to set the duty cycle for the given channel.
  extern task set_duty_cycle(int unsigned channel, bit [15:0] A, bit [15:0] B);

  // Use a CSR write to set BLINK_PARAM for the given channel
  extern task set_blink(int unsigned channel, bit [15:0] A, bit [15:0] B);

  // Use a CSR write to set PWM_PARAM for the given channel.
  extern task set_param(int unsigned channel, param_reg_t value);

  // Return a randomized duty cycle where both fields are nonzero.
  extern virtual function dc_blink_t rand_pwm_duty_cycle();

  // Return a randomized blink duty cycle where both fields are nonzero.
  //
  // Also ensure that the sum of A and B for the blink duty cycle fits in 16 bits. Similarly, ensure
  // that BLINK.B + DUTY_CYCLE.A fits in 16 bits (taking the channel's duty cycle as an argument).
  // This is to prevent counter overflow in both cases.
  extern virtual function dc_blink_t rand_pwm_blink(dc_blink_t duty_cycle);

  // Inject cycles of delay, disabling the main clock for a time in the middle if enable is true.
  extern task low_power_mode(bit enable, uint cycles);

  // Shutdown the dut in a way that helps the last item to finish gracefully.
  extern task shutdown_dut();
endclass : pwm_base_vseq

function pwm_base_vseq::new (string name = "");
  super.new(name);
endfunction

task pwm_base_vseq::apply_reset(string kind = "HARD");
  fork
    if (kind == "HARD" || kind == "TL_IF") begin
      super.apply_reset("HARD");
    end
    if (kind == "HARD" || kind == "CORE_IF") begin
      cfg.clk_rst_core_vif.apply_reset();
    end
  join
endtask

task pwm_base_vseq::apply_resets_concurrently(int reset_duration_ps = 0);
  cfg.clk_rst_core_vif.drive_rst_pin(0);
  super.apply_resets_concurrently(cfg.clk_rst_core_vif.clk_period_ps);
  cfg.clk_rst_core_vif.drive_rst_pin(1);
endtask

task pwm_base_vseq::set_cfg_reg(bit [26:0] ClkDiv, bit [3:0] DcResn, bit CntrEn);
  ral.cfg.clk_div.set(ClkDiv);
  ral.cfg.dc_resn.set(DcResn);
  ral.cfg.cntr_en.set(CntrEn);
  csr_update(ral.cfg);
  foreach(cfg.m_pwm_monitor_cfg[i]) begin
    cfg.m_pwm_monitor_cfg[i].resolution = DcResn;
  end
endtask

task pwm_base_vseq::rand_pwm_cfg_reg();
  bit [26:0] ClkDiv = $urandom_range(0, int'(MAX_CLK_DIV));
  bit [3:0]  DcResn = $urandom_range(0, 14);
  bit        CntrEn = 1'b1;
  set_cfg_reg(ClkDiv, DcResn, CntrEn);
endtask

task pwm_base_vseq::set_ch_invert(bit [PWM_NUM_CHANNELS-1:0] enables);
  csr_wr(.ptr(ral.invert[0]), .value(enables));
  foreach (enables[ii]) begin
    cfg.m_pwm_monitor_cfg[ii].invert = enables[ii];
  end
endtask

task pwm_base_vseq::set_ch_enables(bit [PWM_NUM_CHANNELS-1:0] enables);
  csr_wr(.ptr(ral.pwm_en[0]), .value(enables));
  foreach (enables[ii]) begin
    cfg.m_pwm_monitor_cfg[ii].active = enables[ii];
  end
endtask

task pwm_base_vseq::set_duty_cycle(int unsigned channel, bit [15:0] A, bit [15:0] B);
  `DV_CHECK_FATAL(channel < NOutputs)

  ral.duty_cycle[channel].set({B, A});
  csr_update(ral.duty_cycle[channel]);
endtask

task pwm_base_vseq::set_blink(int unsigned channel, bit [15:0] A, bit [15:0] B);
  `DV_CHECK_FATAL(channel < NOutputs)

  ral.blink_param[channel].set({B, A});
  csr_update(ral.blink_param[channel]);
endtask

task pwm_base_vseq::set_param(int unsigned channel, param_reg_t value);
  `DV_CHECK_FATAL(channel < NOutputs)

  ral.pwm_param[channel].blink_en.set(value.BlinkEn);
  ral.pwm_param[channel].htbt_en.set(value.HtbtEn);
  ral.pwm_param[channel].phase_delay.set(value.PhaseDelay);
  csr_update(ral.pwm_param[channel]);
endtask // set_param

function dc_blink_t pwm_base_vseq::rand_pwm_duty_cycle();
  dc_blink_t value;
  value.A = $urandom_range(1, int'(MAX_16));
  value.B = $urandom_range(1, int'(MAX_16));
  return value;
endfunction

function dc_blink_t pwm_base_vseq::rand_pwm_blink(dc_blink_t duty_cycle);
  dc_blink_t blink;
  blink.B = $urandom_range(0, int'(MAX_16));
  blink.A = $urandom_range(0, int'(MAX_16));
  return blink;
endfunction

task pwm_base_vseq::low_power_mode(bit enable, uint cycles);
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

task pwm_base_vseq::shutdown_dut();
  // Disable all PWM outputs.
  `uvm_info(`gfn, $sformatf("Disabling all channels"), UVM_HIGH)
  set_ch_enables(32'h0);
  // Stop the phase counter.
  ral.cfg.cntr_en.set(1'b0);
  csr_update(ral.cfg);
  dut_shutdown();
endtask
