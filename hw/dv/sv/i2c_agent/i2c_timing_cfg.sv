// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_timing_cfg extends uvm_object;
  `uvm_object_utils(i2c_timing_cfg)

  /////////////////////
  // CLASS VARIABLES //
  /////////////////////

  // Timing //

  uint f_clk_i; // Input clock frequency
  time t_clk_i; // Input clock period (can only store down to the `timescale precision, 1ns)

  speed_mode_e speed_mode;

  // Desired Values
  uint scl_frequency;
  time scl_period;
  uint scl_period_ratio;
  // Actual/Expected Values
  uint coerced_scl_frequency;
  uint coerced_scl_period_cycles;

  rand minmax_abs_timing_cfg_t abstc; // Absolute spec'd timing parameters
  rand minmax_cycles_timing_cfg_t limcyctc;
  rand cycles_timing_cfg_t tc; // Actual register values written to DUT.
  rand timing_cfg_t dtc; // Timing parameters derived from the minimal set, used by the agent.

  // These basic min/max values are used to constrain the timing parameters to
  // a sensible range. This can be changed on a test-by-test basis, but should
  // function as sensible defaults to prevent very-large randomized values from
  // making simulations take an eternity.
  uint i2c_min_timing = 10;
  uint i2c_max_timing = 50;
  uint i2c_time_range = i2c_max_timing - i2c_min_timing;

  // Error Detection //

  // Bits to control interference and unstable interrupts
  //
  // set en_sda_unstable to allow sda_unstable irq is triggered
  bit  en_sda_unstable     = 1'b0;
  // set en_scl_interference to allow scl_interference irq is triggered
  bit  en_scl_interference = 1'b0;
  // set en_sda_interference to allow sda_interference irq is triggered
  bit  en_sda_interference = 1'b0;

  // Assertion probability (in percentages)
  uint i2c_prob_sda_unstable     = 30;
  uint i2c_prob_sda_interference = 30;
  uint i2c_prob_scl_interference = 70;

  // These variables create signalling errors to test error-detection features.
  rand uint t_sda_unstable;     // sda     unstable time during the posedge_clock
  rand uint t_sda_interference; // sda interference time during the posedge_clock
  rand uint t_scl_interference; // scl interference time during the posedge_clock
  rand uint prob_sda_unstable;     // These probabilites are given as percentages
  rand uint prob_sda_interference;
  rand uint prob_scl_interference;

  // This bit can be set to generate stimulus where the Agent (in HOST mode)
  // stretches SCL excessively. We can use this to test certain interrupts in the DUT.
  bit  host_stretch_test_mode = 1'b0;

  /////////////////
  // CONSTRAINTS //
  /////////////////

  // Basic set of default constraints that avoids tests taking
  // too long with very-large delays on a slow bus.
  // These can be disabled for max-perf tests, timeouts, etc.
  constraint timing_val_minmax_c {
    tc.thigh   inside {[i2c_min_timing : i2c_max_timing]};
    tc.tlow    inside {[i2c_min_timing : i2c_max_timing]};
    tc.t_r     inside {[i2c_min_timing : i2c_max_timing]};
    tc.t_f     inside {[i2c_min_timing : i2c_max_timing]};
    tc.thd_sta inside {[i2c_min_timing : i2c_max_timing]};
    tc.tsu_sto inside {[i2c_min_timing : i2c_max_timing]};
    tc.tsu_dat inside {[i2c_min_timing : i2c_max_timing]};
    tc.thd_dat inside {[i2c_min_timing : i2c_max_timing]};
    tc.t_buf   inside {[i2c_min_timing : i2c_max_timing]};
  }
  constraint tsu_sta_minmax_c {
    tc.tsu_sta inside {[i2c_min_timing : i2c_max_timing]};
  }

  // DUT Implementation Limitations
  constraint implementation_c {
    solve tc.t_r, tc.tsu_dat, tc.thd_dat before tc.tlow;
    solve tc.t_r, tc.tsu_sta             before tc.t_buf;

    // > 'tlow' must be at least 2 greater than the sum of (tsu_dat + t_r + thd_dat)
    // > because the flopped outputs of the FSM (see #15003) reduces tClockLow by 1.
    tc.tlow >= (tc.tsu_dat + tc.t_r + tc.thd_dat) + 2;

    // Minimum values to accommodate round-trip latency through the IP.
    tc.tlow >= 3;
    tc.thigh >= 4; // This is required to guarantee we can detect a Target clock-stretching.

    // Satisfy the Start/Stop decoder, which rejects decoding Start/Stop symbols if SCL
    // changes after SDA within "thd_dat" cycles (+1 for CDC skew)
    tc.thd_sta > tc.thd_dat + 1;
    tc.t_buf   > tc.thd_dat + 1;

    // tHoldStop must be at least 2 cycles, therefore 't_r + t_buf - tsu_sta >= 2'
    // in order for the STOP condition to propogate to the FSM via the flop
    tc.t_r + tc.t_buf - tc.tsu_sta >= 2;
  }

  constraint agent_c {
    // If we are generating a fixed_period SCL in the agent, we need the clock pulses
    // to be at-least long enough to contain an RSTART condition to chain transfers
    // together.
    tc.thigh >= tc.tsu_sta + tc.t_f + tc.thd_sta;
  }

  constraint error_stimulus_c {
    solve tc.t_r, tc.t_f, tc.thigh before t_sda_unstable, t_sda_interference;
    t_sda_unstable     inside {[0 : tc.t_r + tc.thigh + tc.t_f - 1]};
    t_sda_interference inside {[0 : tc.t_r + tc.thigh + tc.t_f - 1]};
    t_scl_interference inside {[0 : tc.t_r + tc.thigh + tc.t_f - 1]};
  }

  constraint t_timeout_c {
    tc.tTimeout inside {[i2c_min_timing : i2c_max_timing]};
  }

  constraint spec_minimums_c {
    tc.tsu_sta == limcyctc.min.tsu_sta;
    tc.thd_sta == limcyctc.min.thd_sta;
    tc.tsu_dat == limcyctc.min.tsu_dat;
    // thd_dat only has non-zero specifed minimum value in one configuration:
    // - Standard-mode for CBUS-compatible controllers
    tc.thd_sta == limcyctc.min.thd_sta;
    tc.tsu_sto == limcyctc.min.tsu_sto;

    tc.thigh >= limcyctc.min.thigh;
    tc.tlow  >= limcyctc.min.tlow;
    tc.t_r   >= limcyctc.min.t_r;
    tc.t_f   >= limcyctc.min.t_f;
  }

  constraint spec_maximums_c {
    tc.t_r   <= limcyctc.max.t_r;
    tc.t_f   <= limcyctc.max.t_f;
  }

  constraint prob_error_intr_c {
    prob_sda_unstable     dist {0 :/ (100 - i2c_prob_sda_unstable),
                                1 :/        i2c_prob_sda_unstable};
    prob_sda_interference dist {0 :/ (100 - i2c_prob_sda_interference),
                                1 :/        i2c_prob_sda_interference};
    prob_scl_interference dist {0 :/ (100 - i2c_prob_scl_interference),
                                1 :/        i2c_prob_scl_interference};
  }

  /////////////
  // METHODS //
  /////////////

  function new (string name = "");
    super.new(name);
    // The following constraints are disabled by default.
    spec_minimums_c.constraint_mode(0);
    spec_maximums_c.constraint_mode(0);
  endfunction : new

  function void pre_randomize();
    super.pre_randomize();

    // Set the nominal frequency.
    // - Ensure the input clock frequency is high enough to meet minimum
    //   thigh and tlow cycle counts for a given mode.

    // Below 4 MHz, we cannot do better than the Standard speed mode.
    // For Fast, need at least 4 MHz:
    //  - tlow  = 6
    //  - thigh = 3
    //  - t_r   = 2
    //  - t_f   = 2
    // ...to satisfy all specs with high enough thigh and tlow to satisfy
    // the round-trip time (both greater than 3 cycles).
    // This yields a nominal I2C frequency of 325 kHz (325 / 400 kHz == 81.3%).

    // For FastPlus, need at least 8 MHz:
    // - tlow  = 4
    // - thigh = 3
    // - t_r   = 1
    // - t_f   = 1
    // ...to satisfy all specs with high enough thigh and tlow to satisfy
    // the round-trip time (both greater than 3 cycles).
    // That yields a nominal I2C frequency of 889 kHz (889 / 1000 kHz == 88.9%).

    // The true, coerced value will be determined in post_randomize().
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(speed_mode,
      if (f_clk_i <= 4_000_000)      {speed_mode inside {Standard}};
      else if (f_clk_i <= 8_000_000) {speed_mode inside {Standard, Fast}};
      else                           {speed_mode inside {Standard, Fast, FastPlus}};
    )
    case (speed_mode)
      Standard: scl_frequency =   100_000;
      Fast:     scl_frequency =   400_000;
      FastPlus: scl_frequency = 1_000_000;
    endcase
    scl_period_ratio = $ceil(real'(f_clk_i) / real'(scl_frequency));

    // Get the spec'd limits for this speedmode.
    get_spec_timing_cfg(speed_mode);
  endfunction : pre_randomize

  function void post_randomize();
    super.post_randomize();
    // Derived Timing Parameters
    dtc = get_derived_timing_cfg();
    get_derived_error_stimulus();

    // Ensure these parameters must be greater than zero
    `DV_CHECK_GT_FATAL(dtc.tClockLow, 0)
    `DV_CHECK_GT_FATAL(dtc.tClockStop, 0)
    `DV_CHECK_GT_FATAL(dtc.tHoldStop, 0)

    // Coerce value after quantization. Actual frequency is different from the
    // randomized setting, due to the granularity of the dividers.
    coerced_scl_period_cycles = tc.tlow + tc.t_r + tc.thigh + tc.t_f;
    coerced_scl_frequency    = f_clk_i / coerced_scl_period_cycles;

    `uvm_info(`gfn, "post_randomize() : Newly randomized timing properties:", UVM_LOW)
    `uvm_info(`gfn, $sformatf("speed_mode                       = %10s",
      speed_mode.name()), UVM_LOW)
    `uvm_info(`gfn, $sformatf("scl (frequency) (desired)        = %10.2f MHz",
      (scl_frequency / 1e6)), UVM_LOW)
    `uvm_info(`gfn, $sformatf("scl (period)    (desired)        = %10t",
      (1s / scl_frequency)), UVM_LOW)
    `uvm_info(`gfn, $sformatf("clk (frequency)                  = %10.2f MHz",
      (f_clk_i / 1e6)), UVM_LOW)
    `uvm_info(`gfn, $sformatf("clk (period)                     = %10t",
      (1s / f_clk_i)), UVM_LOW)
    `uvm_info(`gfn, $sformatf("scl/clk period ratio             = %10.2f",
      (real'(f_clk_i) / real'(scl_frequency))), UVM_LOW)
    `uvm_info(`gfn, $sformatf("scl/clk period ratio (quantized) = %10d",
      scl_period_ratio), UVM_LOW)
    `uvm_info(`gfn, $sformatf("scl (period)    (coerced)        = %10d cycles",
      coerced_scl_period_cycles), UVM_LOW)
    `uvm_info(`gfn, $sformatf("scl (period)    (coerced)        = %10t",
      (coerced_scl_period_cycles * (1s / f_clk_i))), UVM_LOW)
    `uvm_info(`gfn, $sformatf("scl (frequency) (coerced)        = %10d Hz",
      coerced_scl_frequency), UVM_LOW)

    print_time_property(tc);
    print_derived_time_property(dtc);
  endfunction : post_randomize

  function automatic void get_spec_timing_cfg(speed_mode_e sm); // {Standard,Fast,FastPlus}
    // Absolute Timing Parameters
    abstc.min.thigh   = get_thigh_min (sm);
    abstc.min.tlow    = get_tlow_min  (sm);
    abstc.min.t_r     = get_tr_min    (sm);
    abstc.min.t_f     = get_tf_min    (sm);
    abstc.min.tsu_sta = get_tsusta_min(sm);
    abstc.min.thd_sta = get_thdsta_min(sm);
    abstc.min.tsu_dat = get_tsudat_min(sm);
    abstc.min.thd_dat = get_thddat_min(sm);
    abstc.min.tsu_sto = get_tsusto_min(sm);
    abstc.min.t_buf   = get_tbuf_min  (sm);
    abstc.max.t_r     = get_tr_max    (sm);
    abstc.max.t_f     = get_tf_max    (sm);

    // Calculate the timing parameters in terms of the input clock
    // Here is where we apply appropriate rounding.

    // Minimums
    limcyctc.min.thigh   = $ceil(real'(abstc.min.thigh)   / real'(1s / f_clk_i));
    limcyctc.min.tlow    = $ceil(real'(abstc.min.tlow)    / real'(1s / f_clk_i));
    limcyctc.min.t_r     = $ceil(real'(abstc.min.t_r)     / real'(1s / f_clk_i));
    limcyctc.min.t_f     = $ceil(real'(abstc.min.t_f)     / real'(1s / f_clk_i));
    limcyctc.min.tsu_sta = $ceil(real'(abstc.min.tsu_sta) / real'(1s / f_clk_i));
    limcyctc.min.thd_sta = $ceil(real'(abstc.min.thd_sta) / real'(1s / f_clk_i));
    limcyctc.min.tsu_dat = $ceil(real'(abstc.min.tsu_dat) / real'(1s / f_clk_i));
    limcyctc.min.thd_dat = $ceil(real'(abstc.min.thd_dat) / real'(1s / f_clk_i));
    limcyctc.min.tsu_sto = $ceil(real'(abstc.min.tsu_sto) / real'(1s / f_clk_i));
    limcyctc.min.t_buf   = $ceil(real'(abstc.min.t_buf)   / real'(1s / f_clk_i));

    // Maximums
    limcyctc.max.t_r     = $ceil(real'(abstc.max.t_r)     / real'(1s / f_clk_i));
    limcyctc.max.t_f     = $ceil(real'(abstc.max.t_f)     / real'(1s / f_clk_i));
  endfunction : get_spec_timing_cfg

  function automatic timing_cfg_t get_derived_timing_cfg();
    timing_cfg_t dtc;

    // The derived parameters for the agent are largely the same as the parameters programmed
    // into the DUT, as our if/agent is also synchronous to the source clk_i.
    // Therefore, these calculations largely match the calculations in `i2c_fsm.sv`.
    begin
      timing_cfg_t fsmdtc;
      // IDENTICAL calcs as `i2c_fsm.sv`
      fsmdtc.tSetupStart = tc.t_r + tc.tsu_sta;
      fsmdtc.tHoldStart  = tc.t_f + tc.thd_sta;
      fsmdtc.tSetupData  = tc.t_r + tc.tsu_dat;
      fsmdtc.tClockStart = tc.thd_dat;
      fsmdtc.tClockLow   = tc.tlow - tc.thd_dat;
      fsmdtc.tClockPulse = tc.t_r + tc.thigh;
      fsmdtc.tClockHigh  = tc.thigh;
      fsmdtc.tHoldBit    = tc.t_f + tc.thd_dat;
      fsmdtc.tClockStop  = tc.t_f + tc.tlow - tc.thd_dat;
      fsmdtc.tSetupStop  = tc.t_r + tc.tsu_sto;
      fsmdtc.tHoldStop   = tc.t_r + tc.t_buf - tc.tsu_sta;
      fsmdtc.eTimeOut    = tc.eTimeout;
      fsmdtc.tTimeOut    = tc.tTimeout;
      dtc = fsmdtc;
    end

    // > The following params are used by the TB/Agent only

    dtc.tSetupBit = tc.t_r + tc.tsu_dat; // aka. tSetupData

    // Select suitable delays when testing clock stretching.
    dtc.tStretchHostClock = gen_num_stretch_host_clks(dtc);

    // Shrink tClockLow because SCL coming from the host side is now flopped. (See #15003)
    // This means, relative to the expectation of the DUT, we have "1 less"
    // cycle of clock time. Specifically, if the DUT drives the clock at cycle 1,
    // the device does not see the clock until cycle 2. This means, the device
    // expectation of how long "low" is now shrunk by 1, since the end point is
    // still fixed.
    dtc.tClockLow -= (dtc.tSetupBit + 1);
    //            -= (t_r + tsu_dat + 1);

    return dtc;
  endfunction : get_derived_timing_cfg

  function void get_derived_error_stimulus();
    // Error Conditions //
    dtc.tSclInterference = (!en_scl_interference) ? 0 : prob_scl_interference * t_scl_interference;
    dtc.tSdaInterference = (!en_sda_interference) ? 0 : prob_sda_interference * t_sda_interference;
    dtc.tSdaUnstable     = (!en_sda_unstable)     ? 0 : prob_sda_unstable     * t_sda_unstable;
  endfunction : get_derived_error_stimulus

  function int gen_num_stretch_host_clks(timing_cfg_t tc);
    // By randomly pulling down scl_o "offset" within [0:2*tc.tTimeOut],
    // 'intr_stretch_timeout_o' interrupt would be generated uniformly.
    // To test this feature more regressive, there might need a dedicated vseq (V2)
    // in which TIMEOUT_CTRL.EN is always set.

    // If Stretch value is greater than 2*tTimeOut, it will create 2 interrupt events.
    // Which can cause false errors in 'host_stretch_testmode'.
    // So, this value should be associated with tTimeout in host stretch testmode
    if (host_stretch_test_mode) begin
      return (tc.tTimeOut + 1);
    end else begin
      return $urandom_range(tc.tClockPulse, tc.tClockPulse + 2*tc.tTimeOut);
    end
  endfunction : gen_num_stretch_host_clks

endclass : i2c_timing_cfg
