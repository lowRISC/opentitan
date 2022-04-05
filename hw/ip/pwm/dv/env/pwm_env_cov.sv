// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class pwm_env_cov extends cip_base_env_cov #(.CFG_T(pwm_env_cfg));
  `uvm_component_utils(pwm_env_cov)

  // the base class provides the following handles for use:
  // pwm_env_cfg: cfg

  // covergroups

  covergroup cfg_cg with function sample(bit [26:0] clkdiv,
                                        bit [3:0]  dcresn,
                                         bit        cntren);
    clkdiv_cp: coverpoint clkdiv {
      bins minimum_value  = {0};
      bins valid_range[4] = {[0:$]};
      bins maximum_value  = {MAX_27};
    }
    dcresn_cp: coverpoint dcresn {
      bins minimum_value  = {0};
      bins valid_range[4] = {[0:$]};
      bins maximum_value  = {'hF};
    }
    cntren_cp: coverpoint cntren;
    cfg_cg_cross_cp: cross clkdiv_cp, dcresn_cp;
  endgroup : cfg_cg

  covergroup pwm_chan_en_inv_cg with function sample(bit [PWM_NUM_CHANNELS-1:0] en_chan,
                                                     bit [PWM_NUM_CHANNELS-1:0] inv_chan);
    // channels and inverts
    en_chan_cp: coverpoint en_chan {
      bins en_single_chan[6] = {'h1, 'h2, 'h4, 'h8, 'h10, 'h20};
      bins en_all_chan       = {'h3F};
      bins valid_range[8]    = {['h3:$]};
    }
    inv_chan_cp: coverpoint inv_chan {
      bins en_single_chan[6] = {'h1, 'h2, 'h4, 'h8, 'h10, 'h20};
      bins en_all_chan       = {'h3F};
      bins valid_range[8]    = {['h3:$]};
    }
    en_inv_cross_cp: cross en_chan_cp, inv_chan_cp {
      bins inverted_enabled = en_inv_cross_cp with (en_chan_cp == inv_chan_cp);
      ignore_bins not_eq    = en_inv_cross_cp with (en_chan_cp != inv_chan_cp);
    }
  endgroup : pwm_chan_en_inv_cg

  covergroup pwm_per_channel_cg with function sample(
    bit [PWM_NUM_CHANNELS-1:0] en_chan,
    bit [PWM_NUM_CHANNELS-1:0] inv_chan,
    bit [15:0]                 phase_delay,
    bit                        blink_en,
    bit                        htbt_en,
    bit [15:0]                 duty_cycle_a,
    bit [15:0]                 duty_cycle_b,
    bit [15:0]                 blink_x,
    bit [15:0]                 blink_y
    );

    // sampled channel
    channels_cp: coverpoint en_chan {
      bins channel_1 = {'h1};
      bins channel_2 = {'h2};
      bins channel_3 = {'h3};
      bins channel_4 = {'h4};
      bins channel_5 = {'h5};
      bins channel_6 = {'h6};
    }

    // pwm_params
    phase_delay_cp: coverpoint phase_delay {
      bins minimum_value = {0};
      bins low_range     = {[0:(MAX_16/3)]};
      bins mid_range     = {[(MAX_16/3):((2*MAX_16)/3)]};
      bins high_range    = {[((2*MAX_16)/3):$]};
      bins maximum_value = {MAX_16};
    }
    phase_delay_per_channel_cross_cp: cross phase_delay_cp, channels_cp;

    htbt_en_cp: coverpoint htbt_en {
      bins enabled  = {1};
      bins disabled = {0};
    }
    htbt_en_per_channel_cross_cp: cross htbt_en_cp, channels_cp;

    blink_en_cp: coverpoint blink_en {
      bins enabled  = {1};
      bins disabled = {0};
    }
    blink_en_per_channel_cross_cp: cross blink_en_cp, channels_cp;

    // htbt can only be enabled when blink is also enabled
    htbt_blink_en_cp: cross blink_en_cp, htbt_en_cp {
      ignore_bins undefined_state = (binsof(blink_en_cp) && binsof(htbt_en_cp))
                                      with ((blink_en_cp == 0) && (htbt_en_cp == 1));
    }

    // duty cycles
    duty_cycle_a_cp: coverpoint duty_cycle_a {
      bins minimum_value = {0};
      bins low_range     = {[0:(MAX_16/3)]};
      bins mid_range     = {[(MAX_16/3):((2*MAX_16)/3)]};
      bins high_range    = {[((2*MAX_16)/3):$]};
      bins maximum_value = {MAX_16};
    }
    duty_a_per_channel_cross_cp: cross duty_cycle_a_cp, channels_cp;

    duty_cycle_b_cp: coverpoint duty_cycle_b {
      bins minimum_value = {0};
      bins low_range     = {[0:(MAX_16/3)]};
      bins mid_range     = {[(MAX_16/3):((2*MAX_16)/3)]};
      bins high_range    = {[((2*MAX_16)/3):$]};
      bins maximum_value = {MAX_16};
    }
    duty_b_per_channel_cross_cp: cross duty_cycle_b_cp, channels_cp;

    dc_a_b_cross_cp: cross duty_cycle_a_cp, duty_cycle_b_cp {
      bins a_lt_b = (binsof(duty_cycle_a_cp) && binsof(duty_cycle_b_cp))
                      with (duty_cycle_a_cp < duty_cycle_b_cp);
      bins a_gt_b = (binsof(duty_cycle_a_cp) && binsof(duty_cycle_b_cp))
                      with (duty_cycle_a_cp > duty_cycle_b_cp);
      bins a_eq_b = (binsof(duty_cycle_a_cp) && binsof(duty_cycle_b_cp))
                      with (duty_cycle_a_cp == duty_cycle_b_cp);
    }
    dc_a_b_cross_per_channel_cross_cp: cross dc_a_b_cross_cp, channels_cp;

    // blink parameter
    blink_x_cp: coverpoint blink_x {
      bins minimum_value = {0};
      bins low_range     = {[0:(MAX_16/3)]};
      bins mid_range     = {[(MAX_16/3):((2*MAX_16)/3)]};
      bins high_range    = {[((2*MAX_16)/3):$]};
      bins maximum_value = {MAX_16};
    }
    blink_x_per_channel_cross_cp: cross blink_x_cp, channels_cp;

    blink_y_cp: coverpoint blink_y {
      bins minimum_value = {0};
      bins low_range     = {[0:(MAX_16/3)]};
      bins mid_range     = {[(MAX_16/3):((2*MAX_16)/3)]};
      bins high_range    = {[((2*MAX_16)/3):$]};
      bins maximum_value = {MAX_16};
    }
    blink_y_per_channel_cross_cp: cross blink_y_cp, channels_cp;

    blink_x_y_cross_cp: cross blink_x_cp, blink_y_cp {
      bins x_lt_y = (binsof(blink_x_cp) && binsof(blink_y_cp))
                      with (blink_x_cp < blink_y_cp);
      bins x_gt_y = (binsof(blink_x_cp) && binsof(blink_y_cp))
                      with (blink_x_cp > blink_y_cp);
      bins x_eq_y = (binsof(blink_x_cp) && binsof(blink_y_cp))
                      with (blink_x_cp == blink_y_cp);
    }
    blink_x_y_cross_per_channel_cross_cp: cross blink_x_y_cross_cp, channels_cp;
  endgroup : pwm_per_channel_cg

  covergroup lowpower_cg with function sample(bit tl_clk_gate,
                                              bit pwm_if_pulse);
    pwm_pulse_cp: coverpoint pwm_if_pulse {
      bins pulses = (0, 1 => 1, 0);
    }
    tl_clk_gated_cp: coverpoint tl_clk_gate {
      bins gated = {1};
      ignore_bins not_gated = {0};
    }
    pulse_while_gated_cross_cp: cross pwm_pulse_cp, tl_clk_gated_cp {
      option.at_least = 1;
    }
  endgroup : lowpower_cg

  covergroup clock_cg with function sample(int core_clk_freq, int tl_clk_freq);
    core_clk_cp: coverpoint core_clk_freq {
      bins valid_range[10] = {[0:50]};
    }
    tl_clk_cp: coverpoint tl_clk_freq {
      bins valid_range[1] = {[0:50]};
    }
    tl_core_eq_cross_cp: cross core_clk_cp, tl_clk_cp;
  endgroup : clock_cg

  function new(string name, uvm_component parent);
    super.new(name, parent);
    //regwen_cg = new(); // TODO stage V2S
    cfg_cg = new();
    pwm_chan_en_inv_cg = new();
    pwm_per_channel_cg = new();
    lowpower_cg = new();
    clock_cg = new();
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // [or instantiate covergroups here]
    // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
    // See cip_base_env_cov for details
  endfunction

endclass
