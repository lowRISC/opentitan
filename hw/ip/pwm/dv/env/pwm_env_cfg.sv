// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_env_cfg extends cip_base_env_cfg #(.RAL_T(pwm_reg_block));

  `uvm_object_utils_begin(pwm_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // config
  pwm_seq_cfg seq_cfg;
  // virtual ifs
  virtual clk_rst_if clk_rst_core_vif;
  virtual pwm_if#(PWM_NUM_CHANNELS) pwm_vif;
  // variables
  uint ok_to_end_delay_ns = 3000;    // drained time of phase_ready_to_end
  bit en_monitor = 1'b1;             // enable monitor
  bit [31:0] num_pulses;             // number of generated pulse
  bit [PWM_NUM_CHANNELS-1:0] invert; // invert pulse
  int core_clk_freq_mhz;             // core clock freq

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);

    // create seq_cfg
    seq_cfg = pwm_seq_cfg::type_id::create("seq_cfg");
  endfunction

  // clk_core_freq_mhz is assigned by
  // - a slower frequency in range [bus_clock*scale : bus_clock] if en_random is set (scale <= 1)
  // - bus_clock frequency otherwise
  virtual function int get_clk_core_freq(real core_clk_ratio, uint en_random = 1);
    int clk_core_min, clk_core_max, clk_core_mhz;

    if (en_random) begin
      `DV_CHECK_LE(core_clk_ratio, 1)
      clk_core_max = clk_rst_vif.clk_freq_mhz;
      clk_core_min = int'(core_clk_ratio * real'(clk_rst_vif.clk_freq_mhz));
      clk_core_mhz = $urandom_range(clk_core_min, clk_core_max);
    end else begin
      clk_core_mhz = clk_rst_vif.clk_freq_mhz;
    end
    `uvm_info(`gfn, $sformatf("clk_bus %0d Mhz, clk_core %0d Mhz",
        clk_rst_vif.clk_freq_mhz, clk_core_mhz), UVM_DEBUG)
    `DV_CHECK_LE(clk_core_mhz, clk_rst_vif.clk_freq_mhz)
    return clk_core_mhz;
  endfunction : get_clk_core_freq

  virtual function void print_pwm_regs(string msg, pwm_regs_t regs,
                                       int channel, bit en_print = 1'b1);
    if (regs.en[channel] && en_print) begin
      string str;
      str = $sformatf("\n>>> %s: channel %0d configuration", msg, channel);
      str = {str, $sformatf("\n  pwm_mode        %s",  regs.pwm_mode[channel].name())};
      str = {str, $sformatf("\n  pwm_en          %s",  regs.en[channel] ? "Enable" : "Disable")};
      str = {str, $sformatf("\n  clk_div         %0d", regs.clk_div)};
      str = {str, $sformatf("\n  dc_resn         %0d", regs.dc_resn)};
      str = {str, $sformatf("\n  num_pulses      %0d", regs.num_pulses)};
      str = {str, $sformatf("\n  beat_cycle      %0d", regs.beat_cycle)};
      str = {str, $sformatf("\n  pulse_cycle     %0d", regs.pulse_cycle)};
      str = {str, $sformatf("\n  pulse_duty      %0d", regs.pulse_duty[channel])};
      str = {str, $sformatf("\n  invert          %b",  regs.invert[channel])};
      str = {str, $sformatf("\n  blink_en        %b",  regs.blink_en[channel])};
      str = {str, $sformatf("\n  htbt_en         %b",  regs.htbt_en[channel])};
      str = {str, $sformatf("\n  phase_delay     %0d", regs.phase_delay[channel])};
      str = {str, $sformatf("\n  duty_cycle_a    %0d", regs.duty_cycle_a[channel])};
      str = {str, $sformatf("\n  duty_cycle_b    %0d", regs.duty_cycle_b[channel])};
      str = {str, $sformatf("\n  blink_param_x   %0d", regs.blink_param_x[channel])};
      str = {str, $sformatf("\n  blink_param_y   %0d", regs.blink_param_y[channel])};
      `uvm_info(`gfn, $sformatf("%s", str), UVM_LOW)
    end
  endfunction : print_pwm_regs

endclass : pwm_env_cfg
