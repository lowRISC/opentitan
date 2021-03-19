// Copyright lowRISC contributors.
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
`endif

  bit drive_clk;              // enable clk generation
  logic o_clk;                // output clk

  bit drive_rst_n;            // enable rst_n generation
  logic o_rst_n;              // output rst_n

  // clk params
  bit clk_gate      = 1'b0;   // clk gate signal
  int clk_period_ps = 20_000; // 50MHz default
  real clk_freq_mhz = 50;     // 50MHz default
  int duty_cycle    = 50;     // 50% default
  int max_jitter_ps = 1000;   // 1ns default
  bit recompute     = 1'b1;   // compute half periods when period/freq/duty are changed
  int clk_hi_ps;              // half period hi in ps
  int clk_lo_ps;              // half period lo in ps
  int jitter_chance_pc = 0;   // jitter chance in percentage on clock edge - disabled by default
  bit sole_clock = 1'b0;      // if true, this is the only clock in the system

  // use IfName as a part of msgs to indicate which clk_rst_vif instance
  string msg_id = {"clk_rst_if::", IfName};

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

  // wait for rst_n to assert and then deassert
  task automatic wait_for_reset(bit wait_negedge = 1'b1, bit wait_posedge = 1'b1);
    if (wait_negedge && ($isunknown(rst_n) || rst_n === 1'b1)) @(negedge rst_n);
    if (wait_posedge && (rst_n === 1'b0)) @(posedge rst_n);
  endtask

  // set the clk frequency in khz
  function automatic void set_freq_khz(int freq_khz);
    clk_freq_mhz = $itor(freq_khz) / 1000;
    clk_period_ps = 1000_000 / clk_freq_mhz;
    recompute = 1'b1;
  endfunction

  // set the clk frequency in mhz
  function automatic void set_freq_mhz(int freq_mhz);
    set_freq_khz(freq_mhz * 1000);
  endfunction

  // call this function at t=0 (from tb top) to enable clk and rst_n to be driven
  function automatic void set_active(bit drive_clk_val = 1'b1, bit drive_rst_n_val = 1'b1);
    time t = $time;
    if (t == 0) begin
      drive_clk = drive_clk_val;
      drive_rst_n = drive_rst_n_val;
    end
    else begin
`ifdef VERILATOR
      $error({msg_id, "this function can only be called at t=0"});
`else
      `uvm_fatal(msg_id, "this function can only be called at t=0")
`endif
    end
  endfunction

  // set the clk period in ps
  function automatic void set_period_ps(int period_ps);
    clk_period_ps = period_ps;
    clk_freq_mhz  = 1000_000 / clk_period_ps;
    recompute     = 1'b1;
  endfunction

  // set the duty cycle (1-99)
  function automatic void set_duty_cycle(int duty);
    if (!(duty inside {[1:99]})) begin
`ifdef VERILATOR
      $error({msg_id, $sformatf("duty cycle %0d is not inside [1:99]", duty)});
`else
      `uvm_fatal(msg_id, $sformatf("duty cycle %0d is not inside [1:99]", duty))
`endif
    end
    duty_cycle = duty;
    recompute = 1'b1;
  endfunction

  // set maximum jitter in ps
  function automatic void set_max_jitter_ps(int jitter_ps);
    max_jitter_ps = jitter_ps;
  endfunction

  // set jitter chance in percentage (0 - 100)
  // 0 - dont add any jitter; 100 - add jitter on every clock edge
  function automatic void set_jitter_chance_pc(int jitter_chance);
    if (!(jitter_chance inside {[0:100]})) begin
`ifdef VERILATOR
      $error({msg_id, $sformatf("jitter_chance %0d is not inside [0:100]", jitter_chance)});
`else
      `uvm_fatal(msg_id, $sformatf("jitter_chance %0d is not inside [0:100]", jitter_chance))
`endif
    end
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

  // add jitter to clk_hi and clk_lo half periods based on jitter_chance_pc
  function automatic void add_jitter();
    int jitter_ps;
    if ($urandom_range(1, 100) <= jitter_chance_pc) begin
`ifndef VERILATOR
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(jitter_ps,
          jitter_ps inside {[-1*max_jitter_ps:max_jitter_ps]};, "", msg_id)
`endif
      clk_hi_ps += jitter_ps;
    end
    if ($urandom_range(1, 100) <= jitter_chance_pc) begin
`ifndef VERILATOR
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(jitter_ps,
          jitter_ps inside {[-1*max_jitter_ps:max_jitter_ps]};, "", msg_id)
`endif
      clk_lo_ps += jitter_ps;
    end
  endfunction

  // can be used to override clk/rst pins, e.g. at the beginning of the simulation
  task automatic drive_rst_pin(logic val = 1'b0);
    o_rst_n = val;
  endtask

  // apply reset with specified scheme
  // TODO make this enum?
  // rst_n_scheme
  // 0 - fullly synchronous reset - it is asserted and deasserted on clock edges
  // 1 - async assert, sync dessert (default)
  // 2 - async assert, async dessert
  // 3 - clk gated when reset asserted
  // Note: for power on reset, please ensure pre_reset_dly_clks is set to 0
  // TODO #2338 issue workaround - $urandom call moved from default argument value to function body
  task automatic apply_reset(int pre_reset_dly_clks   = 0,
                             integer reset_width_clks = 'x,
                             int post_reset_dly_clks  = 0,
                             int rst_n_scheme         = 1);
    int dly_ps;
    if ($isunknown(reset_width_clks)) reset_width_clks = $urandom_range(50, 100);
    dly_ps = $urandom_range(0, clk_period_ps);
    wait_clks(pre_reset_dly_clks);
    case (rst_n_scheme)
      0: begin : sync_assert_deassert
        o_rst_n <= 1'b0;
        wait_clks(reset_width_clks);
        o_rst_n <= 1'b1;
      end
      1: begin : async_assert_sync_deassert
        #(dly_ps * 1ps);
        o_rst_n <= 1'b0;
        wait_clks(reset_width_clks);
        o_rst_n <= 1'b1;
      end
      2: begin : async_assert_async_deassert
        #(dly_ps * 1ps);
        o_rst_n <= 1'b0;
        wait_clks(reset_width_clks);
        dly_ps = $urandom_range(0, clk_period_ps);
        #(dly_ps * 1ps);
        o_rst_n <= 1'b1;
      end
      default: begin
`ifdef VERILATOR
        $error({msg_id, $sformatf("rst_n_scheme %0d not supported", rst_n_scheme)});
`else
        `uvm_fatal(msg_id, $sformatf("rst_n_scheme %0d not supported", rst_n_scheme))
`endif
      end
    endcase
    wait_clks(post_reset_dly_clks);
  endtask

  // clk gen
  initial begin
    // start driving clk only after the first por reset assertion. The fork/join means that we'll
    // wait a whole number of clock periods, which means it's possible for the clock to synchronise
    // with the "expected" timestamps.
    bit done;
    fork
      begin
        wait_for_reset(.wait_posedge(1'b0));

        // Wait a short time after reset before starting to drive the clock.
        #1ps;
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
        recompute = 1'b0;
      end
      if (jitter_chance_pc != 0) add_jitter();
      #(clk_lo_ps * 1ps);
      // wiggle output clk if not gated
      if (!clk_gate) o_clk = 1'b1;
      #(clk_hi_ps * 1ps);
      o_clk = 1'b0;
    end
  end

  assign clk   = drive_clk   ? o_clk   : 1'bz;
  assign rst_n = drive_rst_n ? o_rst_n : 1'bz;

endinterface
