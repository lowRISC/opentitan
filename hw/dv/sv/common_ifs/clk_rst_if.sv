// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Interface: clk_rst_if
// Generic clock and reset interface for clock events in various utilities
// It also generates o_clk and o_rst_n signals for driving clk and rst_n in the tb. The advantage is
// clk and rst_n can be completely controlled in course of the simulation.
// This interface provides methods to set freq/period, wait for clk/rst_n, apply rst_n among other
// things. See individual method descriptions below.
// inout clk
// inout rst_n

interface clk_rst_if #(
  parameter string IfName = "main"
) (
  inout clk,
  inout rst_n
);

`ifndef VERILATOR
  // include macros and import pkgs
  `include "dv_macros.svh"
  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import common_ifs_pkg::*;
`endif

  // Enables clock to be generated and driven by this interface.
  bit drive_clk;

  // The internal output clock value.
  logic o_clk;

  // Enables the rst_n to be generated and driven by this interface.
  bit drive_rst_n;

  // The internal output reset value.
  logic o_rst_n;

  // This event is used to start the initial block driving the clock after set_active sets
  // the values of drive_clk and drive_rst_n.
  event set_active_called;

  // Applies clock gating.
  bit clk_gate = 1'b0;

  // The nominal (chosen) frequency (as period in ps) of the driven clock (50MHz by default).
  int clk_period_ps = 20_000;

  // The variation of clock period (mimics uncalibrated clocks), to scale the nominal frequency
  // down. If set to non-zero value, the clock frequency is scaled randomly on every edge.
  int clk_freq_scaling_pc = 0;

  // The percentage chance of freq scaled down randomly on each edge.
  int clk_freq_scaling_chance_pc = 50;

  // Clock frequency is scaled down. This enables the frequency to be randomly scaled up as well.
  //
  // Note: If set, the randomness of the clock frequency being scaled up or down may result in a
  // bigger frequency distribution than the intended clk_freq_scaling_pc setting. For example, 50MHz
  // with 10% scaling may result in pulses that are < 45MHz and > 55MHz wide as well.
  bit clk_freq_scale_up = 1'b0;

  // The computed clock frequency in MHz.
  real clk_freq_mhz = 50;

  // The duty cycle of the clock period as percentage. If jitter and scaling is applied, then the
  // duty cycle will not be maintained.
  int duty_cycle = 50;

  // Maximum jitter applied to each period of the clock - this is expected to be about 20% or less
  // than the clock period.
  // The jitter is divided to two values - plus-jitter and minus-jitter.
  // Plus jitter is the possible time can be added to the clock period, while the minus jittter is
  // the possible time can be subtracted from the clock period.
  //         _________
  // _____:_| :     : |_:_______
  //
  // The actual jitter value is picked randomly within the window
  // {[-max_minus_jitter_ps:max_plus_jitter_ps]}
  // and is added to the time to next edge.
  int max_plus_jitter_ps = 1000;
  int max_minus_jitter_ps = 1000;

  // The percentage chance of jitter occurring on each edge. If 0 (default value), then jitter is
  // disabled altogether. If 100, jitter is computed and applied at every edge.
  int jitter_chance_pc = 0;

  // Internal signal indicating the clock half periods  need to be recomputed.
  bit recompute = 1'b1;

  // Internal signal indicating the amount of time for which the clock stays high / lo in the next
  // cycle.
  int clk_hi_ps;
  int clk_lo_ps;
  real clk_hi_modified_ps;
  real clk_lo_modified_ps;

  // If true, this is the only clock in the system; there is no need to add initial jitter.
  bit sole_clock = 1'b0;

  // use IfName as a part of msgs to indicate which clk_rst_vif instance
  string msg_id = $sformatf("[%m(clk_rst_if):%s]", IfName);

  clocking cb @(posedge clk);
  endclocking

  clocking cbn @(negedge clk);
  endclocking

  // Wait for 'n' clocks based of postive clock edge
  task automatic wait_clks(int num_clks);
    repeat (num_clks) @cb;
  endtask

  // Wait for 'n' clocks based of negative clock edge
  task automatic wait_n_clks(int num_clks);
    repeat (num_clks) @cbn;
  endtask

  // Wait for 'num_clks' clocks based on the positive clock edge or reset, whichever comes first.
  task automatic wait_clks_or_rst(int num_clks);
    fork
      wait_clks(num_clks);
      wait_for_reset(.wait_negedge(1'b1), .wait_posedge(1'b0));
    join_any
  endtask

  // wait for rst_n to assert and then deassert
  task automatic wait_for_reset(bit wait_negedge = 1'b1, bit wait_posedge = 1'b1);
    if (wait_negedge && ($isunknown(rst_n) || rst_n === 1'b1)) @(negedge rst_n);
    if (wait_posedge && (rst_n === 1'b0)) @(posedge rst_n);
  endtask

  // set the clk frequency in khz
  function automatic void set_freq_khz(int freq_khz);
    `DV_CHECK_FATAL(freq_khz > 0, , msg_id)
    clk_freq_mhz = $itor(freq_khz) / 1000;
    clk_period_ps = 1000_000 / clk_freq_mhz;
    recompute = 1'b1;
  endfunction

  // set the clk frequency in mhz
  function automatic void set_freq_mhz(int freq_mhz);
    `DV_CHECK_FATAL(freq_mhz > 0, , msg_id)
    set_freq_khz(freq_mhz * 1000);
  endfunction

  // Set the clk frequency scaling, chance in percentage and scaling up.
  //
  // freq_scaling_pc is a positive integer that determines by what amount (as percentage of the
  // nominal frequency) is the frequency scaled (jittered) down.
  // freq_scaling_chance_pc is a percentage number between 0 and 100 that determines how often is
  // the scaling randomly recomputed and applied.
  // freq_scale_up is a bit that enables the random scaling up of the frequency as well.
  function automatic void set_freq_scaling(int freq_scaling_pc, int freq_scaling_chance_pc = 50,
                                           bit freq_scale_up = 1'b0);
    `DV_CHECK_FATAL(freq_scaling_pc >= 0, , msg_id)
    `DV_CHECK_FATAL(freq_scaling_chance_pc inside {[0:100]}, , msg_id)
    clk_freq_scaling_pc = freq_scaling_pc;
    clk_freq_scaling_chance_pc = freq_scaling_chance_pc;
    clk_freq_scale_up = freq_scale_up;
  endfunction

  // Enables the clock and reset to be driven.
  function automatic void set_active(bit drive_clk_val = 1'b1, bit drive_rst_n_val = 1'b1);
    drive_clk = drive_clk_val;
    drive_rst_n = drive_rst_n_val;
    -> set_active_called;
  endfunction

  // set the clk period in ps
  function automatic void set_period_ps(int period_ps);
    clk_period_ps = period_ps;
    clk_freq_mhz  = 1000_000 / clk_period_ps;
    recompute     = 1'b1;
  endfunction

  // set the duty cycle (1-99)
  function automatic void set_duty_cycle(int duty);
    `DV_CHECK_FATAL(duty inside {[1:99]}, , msg_id)
    duty_cycle = duty;
    recompute = 1'b1;
  endfunction

  // set maximum jitter in ps, separating the plus jitter and the minus jitter.
  //  In default the plus and minus jitters are the same.
  function automatic void set_max_jitter_ps(int plus_jitter_ps,
                                            int minus_jitter_ps = plus_jitter_ps);
    max_plus_jitter_ps = plus_jitter_ps;
    max_minus_jitter_ps = minus_jitter_ps;
  endfunction

  // set jitter chance in percentage (0 - 100)
  // 0 - dont add any jitter; 100 - add jitter on every clock edge
  function automatic void set_jitter_chance_pc(int jitter_chance);
    `DV_CHECK_FATAL(jitter_chance inside {[0:100]}, , msg_id)
    jitter_chance_pc = jitter_chance;
  endfunction

  // Set whether this is the only clock in the system. If true, various bits of timing randomisation
  // are disabled. If there's no other clock to (de)synchronise with, this should not weaken the
  // test at all.
  function automatic void set_sole_clock(bit is_sole = 1'b1);
    sole_clock = is_sole;
  endfunction

  // start / ungate the clk
  task automatic start_clk(bit wait_for_posedge = 1'b0);
    clk_gate = 1'b0;
    if (wait_for_posedge) wait_clks(1);
  endtask

  // stop / gate the clk
  function automatic void stop_clk();
    clk_gate = 1'b1;
  endfunction

  // Scales the clock frequency up and down on every edge.
  function automatic void apply_freq_scaling();
    real scaling;
    real mult = $urandom_range(0, int'(clk_freq_scale_up)) ? 1.0 : -1.0;

    if ($urandom_range(1, 100) <= clk_freq_scaling_chance_pc) begin
      scaling = 1.0 + mult * real'($urandom_range(0, clk_freq_scaling_pc)) / 100;
      clk_hi_modified_ps = clk_hi_ps * scaling;
      scaling = 1.0 + mult * real'($urandom_range(0, clk_freq_scaling_pc)) / 100;
      clk_lo_modified_ps = clk_lo_ps * scaling;
    end
  endfunction

  // Applies jitter to clk_hi and clk_lo half periods based on jitter_chance_pc.
  function automatic void apply_jitter();
    int jitter;
    int plus_jitter;
    int minus_jitter;

    if ($urandom_range(1, 100) <= jitter_chance_pc) begin
      plus_jitter = $urandom_range(0, max_plus_jitter_ps/2);
      minus_jitter = $urandom_range(0, max_minus_jitter_ps/2);
      jitter = ($urandom_range(0, 1) ? plus_jitter : (-1 * minus_jitter));
      clk_hi_modified_ps = clk_hi_ps + jitter;
    end
    if ($urandom_range(1, 100) <= jitter_chance_pc) begin
      plus_jitter = $urandom_range(0, max_plus_jitter_ps/2);
      minus_jitter = $urandom_range(0, max_minus_jitter_ps/2);
      jitter = ($urandom_range(0, 1) ? plus_jitter : (-1 * minus_jitter));
      clk_lo_modified_ps = clk_lo_ps + jitter;
    end
  endfunction

  // can be used to override clk/rst pins, e.g. at the beginning of the simulation
  task automatic drive_rst_pin(logic val = 1'b0);
    o_rst_n = val;
  endtask

  // apply reset with specified scheme
  // Note: for power on reset, please ensure pre_reset_dly_clks is set to 0
  task automatic apply_reset(int pre_reset_dly_clks   = 0,
                             int reset_width_clks = $urandom_range(50, 100),
                             int post_reset_dly_clks  = 0,
                             rst_scheme_e rst_n_scheme  = RstAssertAsyncDeassertSync);
    if (drive_rst_n) begin
      int dly_ps;
      dly_ps = $urandom_range(0, clk_period_ps);
      wait_clks(pre_reset_dly_clks);
      case (rst_n_scheme)
        RstAssertSyncDeassertSync: begin
          o_rst_n <= 1'b0;
          wait_clks(reset_width_clks);
          o_rst_n <= 1'b1;
        end
        RstAssertAsyncDeassertSync: begin
          #(dly_ps * 1ps);
          o_rst_n <= 1'b0;
          wait_clks(reset_width_clks);
          o_rst_n <= 1'b1;
        end
        RstAssertAsyncDeassertASync: begin
          #(dly_ps * 1ps);
          o_rst_n <= 1'b0;
          wait_clks(reset_width_clks);
          dly_ps = $urandom_range(0, clk_period_ps);
          #(dly_ps * 1ps);
          o_rst_n <= 1'b1;
        end
        default: begin
          `dv_fatal($sformatf("rst_n_scheme %0d not supported", rst_n_scheme), msg_id)
        end
      endcase
      wait_clks(post_reset_dly_clks);
    end
  endtask

  // clk gen when the clock is active, so this waits until the set_active function was called.
  initial begin
    // start driving clk only after the first por reset assertion. The fork/join means that we'll
    // wait a whole number of clock periods, which means it's possible for the clock to synchronise
    // with the "expected" timestamps.
    bit done;
    @set_active_called;
    if (drive_clk) begin
      fork
        begin
          // Only wait for reset if driving it, otherwise it may never come.
          if (drive_rst_n) begin
            wait_for_reset(.wait_posedge(1'b0));

            // Wait a short time after reset before starting to drive the clock.
            #1ps;
          end
          o_clk = 1'b0;

          done = 1'b1;
        end
        while (!done) #(clk_period_ps * 1ps);
      join

      // If there might be multiple clocks in the system, wait another (randomised) short time to
      // desynchronise.
      if (!sole_clock) #($urandom_range(0, clk_period_ps) * 1ps);

      forever begin
        if (recompute) begin
          clk_hi_ps = clk_period_ps * duty_cycle / 100;
          clk_lo_ps = clk_period_ps - clk_hi_ps;
          clk_hi_modified_ps = clk_hi_ps;
          clk_lo_modified_ps = clk_lo_ps;
          recompute = 1'b0;
        end
        if (clk_freq_scaling_pc && clk_freq_scaling_chance_pc) apply_freq_scaling();
        if (jitter_chance_pc) apply_jitter();
        #(clk_lo_modified_ps * 1ps);
        if (!clk_gate) o_clk = 1'b1;
        #(clk_hi_modified_ps * 1ps);
        o_clk = 1'b0;
      end
    end
  end

  assign clk   = drive_clk   ? o_clk   : 1'bz;
  assign rst_n = drive_rst_n ? o_rst_n : 1'bz;

endinterface
