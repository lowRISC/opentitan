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

  // Tasks overridden from dv_base_vseq.
  extern task apply_reset(string kind = "HARD");
  extern task apply_resets_concurrently(int reset_duration_ps = 0);

  // Set the CFG register with the given ClkDiv, DcResn, CntrEn with a CSR write.
  extern task set_cfg_reg(bit [26:0] ClkDiv, bit [3:0] DcResn, bit CntrEn);

  // Pick a random value for the CFG register with cntr_en=1.
  extern task rand_pwm_cfg_reg();

  // Use a CSR write to set the INVERT bits as requested.
  extern task set_ch_invert(bit [PWM_NUM_CHANNELS-1:0] invert);

  // Use a CSR write to set the PWM_EN bits as requested.
  extern task set_ch_enables(bit [PWM_NUM_CHANNELS-1:0] enables);

  // Use a CSR write to set DUTY_CYCLE for the given channel.
  extern task set_duty_cycle(int unsigned channel, bit [15:0] A, bit [15:0] B);

  // Use a CSR write to set BLINK_PARAM for the given channel
  extern task set_blink(int unsigned channel, bit [15:0] X, bit [15:0] Y);

  // Use a CSR write to set PWM_PARAM for the given channel.
  extern task set_param(int unsigned channel, param_reg_t value);

  // Return a randomized duty cycle.
  extern virtual function duty_cycle_t rand_pwm_duty_cycle();

  // Return randomized blink parameters.
  extern virtual function blink_param_t rand_pwm_blink();

  // Start the clocks of all alert agents.
  extern task start_alert_clks();

  // Stop the clocks of all alert agents.
  extern task stop_alert_clks();

  // Wait for at least the specified number of clock cycles, monitoring and checking the DUT
  // outputs. Optionally engage low power mode in the middle of the test.
  extern virtual task monitor_dut_outputs(bit low_power_mode, uint cycles);

  // Shutdown the dut in a way that helps the last item to finish gracefully.
  extern virtual task shutdown_dut();
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
  `uvm_info(`gfn, $sformatf("ClkDiv 0x%0x DcResn 0x%0x En %0d", ClkDiv, DcResn, CntrEn), UVM_HIGH)
  // Supply the configuration to each of the monitors in advance of the register update.
  foreach (cfg.m_pwm_monitor_cfg[i]) begin
    cfg.m_pwm_monitor_cfg[i].resolution = DcResn;
    cfg.m_pwm_monitor_cfg[i].clk_div = ClkDiv;
    // Monitors continue to operate for disabled channels too, to ensure that they do not produce
    // unintended traffic.
    cfg.m_pwm_monitor_cfg[i].active = CntrEn;
  end
  ral.cfg.clk_div.set(ClkDiv);
  ral.cfg.dc_resn.set(DcResn);
  ral.cfg.cntr_en.set(CntrEn);
  // The monitors detect the (re)starting of the phase counter and use this cue to collect the
  // configuration supplied above.
  csr_update(ral.cfg);
endtask

task pwm_base_vseq::rand_pwm_cfg_reg();
  bit [26:0] ClkDiv = $urandom_range(0, int'(MAX_CLK_DIV));
  bit [3:0]  DcResn = $urandom_range(0, 14);
  bit        CntrEn = 1'b1;
  set_cfg_reg(ClkDiv, DcResn, CntrEn);
endtask

task pwm_base_vseq::set_ch_invert(bit [PWM_NUM_CHANNELS-1:0] invert);
  `uvm_info(`gfn, $sformatf("Invert 0x%0x", invert), UVM_HIGH)
  csr_wr(.ptr(ral.invert[0]), .value(invert));
  foreach (invert[ii]) begin
    cfg.m_pwm_monitor_cfg[ii].invert = invert[ii];
  end
endtask

task pwm_base_vseq::set_ch_enables(bit [PWM_NUM_CHANNELS-1:0] enables);
  `uvm_info(`gfn, $sformatf("Channel enables 0x%0x", enables), UVM_HIGH)
  csr_wr(.ptr(ral.pwm_en[0]), .value(enables));
endtask

task pwm_base_vseq::set_duty_cycle(int unsigned channel, bit [15:0] A, bit [15:0] B);
  `DV_CHECK_FATAL(channel < NOutputs)

  `uvm_info(`gfn, $sformatf("Channel %0d Duty cycles A 0x%0x B 0x%0x", channel, A, B), UVM_HIGH)
  ral.duty_cycle[channel].set({B, A});
  csr_update(ral.duty_cycle[channel]);
endtask

task pwm_base_vseq::set_blink(int unsigned channel, bit [15:0] X, bit [15:0] Y);
  `DV_CHECK_FATAL(channel < NOutputs)

  `uvm_info(`gfn, $sformatf("Channel %0d Blink params X 0x%0x Y 0x%0x", channel, X, Y), UVM_HIGH)
  ral.blink_param[channel].set({Y, X});
  csr_update(ral.blink_param[channel]);
endtask

task pwm_base_vseq::set_param(int unsigned channel, param_reg_t value);
  `DV_CHECK_FATAL(channel < NOutputs)

  ral.pwm_param[channel].blink_en.set(value.BlinkEn);
  ral.pwm_param[channel].htbt_en.set(value.HtbtEn);
  ral.pwm_param[channel].phase_delay.set(value.PhaseDelay);
  csr_update(ral.pwm_param[channel]);
endtask

function duty_cycle_t pwm_base_vseq::rand_pwm_duty_cycle();
  duty_cycle_t value;
  value.A = $urandom_range(0, int'(MAX_16));
  value.B = $urandom_range(0, int'(MAX_16));
  return value;
endfunction

function blink_param_t pwm_base_vseq::rand_pwm_blink();
  blink_param_t blink;
  blink.X = $urandom_range(0, int'(MAX_16));
  blink.Y = $urandom_range(0, int'(MAX_16));
  return blink;
endfunction

// Start the clocks of all alert agents.
task pwm_base_vseq::start_alert_clks();
  foreach (cfg.list_of_alerts[i]) begin
    string alert_name = cfg.list_of_alerts[i];
    // Restart the clock without advancing the simulation time; `alert_esc_agent` runs on two
    // clocks (our TL-UL clock and this internal asynchronous clock).
    cfg.m_alert_agent_cfgs[alert_name].vif.clk_rst_async_if.start_clk(.wait_for_posedge(1'b0));
  end
endtask

// Stop the clocks of all alert agents.
task pwm_base_vseq::stop_alert_clks();
  foreach (cfg.list_of_alerts[i]) begin
    string alert_name = cfg.list_of_alerts[i];
    cfg.m_alert_agent_cfgs[alert_name].vif.clk_rst_async_if.stop_clk();
  end
endtask

// The PWM outputs are required to keep running with the chip in low power mode, meaning that the
// monitor and scoreboard must continue to match predictions successfully when the TL-UL clock is
// not running.
task pwm_base_vseq::monitor_dut_outputs(bit low_power_mode, uint cycles);
  if (low_power_mode) begin
    int unsigned sleep_cycles = $urandom_range(10, cycles / 4);
    bit ping_chk;
    `uvm_info(`gfn, "Running in low power mode...", UVM_MEDIUM)
    cfg.clk_rst_vif.wait_clks(cycles/2);
    // In the middle of the test turn off the TL-UL clk to observe that the PWM outputs continue.
    // as intended.
    `uvm_info(`gfn, "Stopping TL-UL clock", UVM_MEDIUM)
    // We must suspend all alert agents too whilst the DUT is in low power mode because otherwise
    // they will continue trying to send pings to the alert_sender(s) within the DUT, resulting in
    // spurious ping timeouts.
    stop_alert_clks();
    cfg.clk_rst_vif.stop_clk();
    // Use core clk to determine when to turn the TL-UL clk back on.
    cfg.clk_rst_core_vif.wait_clks(sleep_cycles);
    `uvm_info(`gfn, "Resuming TL-UL clock", UVM_MEDIUM)
    // Restart the clock without advancing the simulation time; `alert_esc_agent` runs on two
    // clocks (an internal asynchronous clock and this TL-UL clock).
    cfg.clk_rst_vif.start_clk(.wait_for_posedge(1'b0));
    // Resume the alert agents.
    start_alert_clks();
    cfg.clk_rst_vif.wait_clks(cycles / 2 - sleep_cycles);
  end else begin
    cfg.clk_rst_vif.wait_clks(cycles);
  end
endtask

task pwm_base_vseq::shutdown_dut();
  // Stop the phase counter _before_ we disable the channels because the scoreboard and the DUT
  // are notified of the channel disabling at different times, leading to a potential prediction
  // mismatch.
  set_cfg_reg(0, 0, 1'b0);
  // Disable all PWM outputs.
  `uvm_info(`gfn, $sformatf("Disabling all channels"), UVM_HIGH)
  set_ch_enables(32'h0);
  dut_shutdown();
  `uvm_info(`gfn, $sformatf("Completed DUT shutdown"), UVM_MEDIUM)
endtask
