// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This module should be instantiated within flops of CDC synchronization primitives,
// and allows DV to model real CDC delays within simulations, especially useful at the chip level
// or in IPs that communicate across clock domains.
//
// If not, delay randomization is enabled - the faster of the two clocks is used to latch src_data,
// dst_data is synchronously driven with a random combination of the current src_data and
// the delayed version of src_data.
//
// If a source clock isn't used, the input src_data is latched after a parameterizable latency
// as `src_data_with_latency`, and an internal version of the output data `src_data_delayed` is set
// to this same value after a parameterizable jitter period.
//
// This is meant to model skew between synchronizer bits and wire delay between the src and dst
// flops.
//
// Four different random delay modes are available:
//
// - RandDelayDisable: If this delay mode is picked, this module acts as a passthrough.
//
// - RandDelaySlow: If this delay mode is picked, the output to the dst domain is
//                  continuously driven to `src_data_delayed`.
//
// - RandDelayOnce: If this delay mode is picked, the mask `out_data_mask` used to combine
//                  `src_data_with_latency` and `src_data_delayed` is randomized once at the
//                  start of the simulation.
//
// - RandDelayInterval: If this delay mode is picked, the mask `out_data_mask` used to
//                      combine `src_data_with_latency` and `src_data_delayed` is fully
//                      randomized every `prim_cdc_rand_delay_interval` times the src_data
//                      value changes. If the `prim_cdc_rand_delay_interval` is set to 0,
//                      then out_data_mask is randomized on every src_data change.
//
// DV has control of the weights corresponding to each random delay mode when the delay mode is
// randomized, but can also directly override the delay mode as desired.
//
// DV also has control over whether the source clock is used, the latency, and the jitter values -
// these can be modified through the provided setter tasks.

module prim_cdc_rand_delay #(
    parameter int DataWidth = 1,
    parameter bit UseSourceClock = 1,
    parameter int LatencyPs = 1000,
    parameter int JitterPs = 1000
) (
    input logic                 src_clk,
    input logic [DataWidth-1:0] src_data,

    input logic                   dst_clk,
    output logic [DataWidth-1:0]  dst_data
);

  `ASSERT_INIT(LegalDataWidth_A, DataWidth > 0)
  `ASSERT_INIT(LegalLatencyPs_A, LatencyPs >= 0)
  `ASSERT_INIT(LegalJitterPs_A,  JitterPs >= 0)

`ifdef SIMULATION
`ifndef DISABLE_PRIM_CDC_RAND_DELAY

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  typedef enum bit [1:0] {
    RandDelayModeDisable,
    RandDelayModeSlow,
    RandDelayModeOnce,
    RandDelayModeInterval
  } rand_delay_mode_e;

  rand_delay_mode_e prim_cdc_rand_delay_mode;
  int unsigned prim_cdc_rand_delay_interval = 10;
  int unsigned prim_cdc_rand_delay_disable_weight  = 1;
  int unsigned prim_cdc_rand_delay_slow_weight     = 2;
  int unsigned prim_cdc_rand_delay_once_weight     = 4;
  int unsigned prim_cdc_rand_delay_interval_weight = 3;
  bit [3:0] mode;  // onehot encoded version of prim_cdc_rand_delay_mode.

  int unsigned prim_cdc_jitter_ps = JitterPs;
  int unsigned prim_cdc_latency_ps = LatencyPs;

  logic [DataWidth-1:0] out_data_mask;
  logic [DataWidth-1:0] src_data_with_latency;
  logic [DataWidth-1:0] src_data_delayed;

  function automatic void set_prim_cdc_rand_delay_mode(int val);
    prim_cdc_rand_delay_mode = rand_delay_mode_e'(val);
    update_settings();
  endfunction

  function automatic void set_prim_cdc_rand_delay_interval(int unsigned val);
    prim_cdc_rand_delay_interval = val;
  endfunction

  function automatic void set_prim_cdc_jitter_ps(int val);
    `ASSERT_I(LegalJitter_A, prim_cdc_jitter_ps >= 0)
    prim_cdc_jitter_ps = val;
  endfunction

  function automatic void set_prim_cdc_latency_ps(int val);
    `ASSERT_I(LegalLatencyPs_A, val >= 0)
    prim_cdc_latency_ps = val;
  endfunction

  // Internal method called after prim_cdc_rand_delay_mode is set.
  function automatic void update_settings();
    mode = '0;
    mode[prim_cdc_rand_delay_mode] = 1'b1;
    if (prim_cdc_rand_delay_mode == RandDelayModeSlow) out_data_mask = '1;
    if (prim_cdc_rand_delay_mode == RandDelayModeOnce) fast_randomize(out_data_mask);
  endfunction

  // A slightly more performant version of std::randomize(), using $urandom.
  //
  // Empirically, using std::randomize() has been found to be slower than $urandom, since the latter
  // operates on a fixed data width of 32-bits. There may be an incredibly large number of instances
  // of this module in the DUT, causing this preformance hit to be noticeable. This method
  // randomizes the data piece-wise, 32-bits at a time using $urandom instead.
  function automatic void fast_randomize(output logic [DataWidth-1:0] data);
    for (int i = 0; i < DataWidth; i += 32) data = (data << 32) | $urandom();
  endfunction

  // Retrieves settings via plusargs.
  //
  // prefix is a string prefix to retrieve the plusarg.
  // Returns 1 if prim_cdc_rand_delay_mode was set, else 0.
  function automatic bit get_plusargs(string prefix = "");
    string mode = "";
    int unsigned val;
    if (prefix != "") prefix = {prefix, "."};
    void'($value$plusargs({prefix, "prim_cdc_rand_delay_mode=%0s"}, mode));
    `ASSERT_I(ValidMode_A, mode inside {"", "disable", "slow", "once", "interval"})
    void'($value$plusargs({prefix, "prim_cdc_rand_delay_interval=%0d"},
                          prim_cdc_rand_delay_interval));
    void'($value$plusargs({prefix, "prim_cdc_rand_delay_disable_weight=%0d"},
                          prim_cdc_rand_delay_disable_weight));
    void'($value$plusargs({prefix, "prim_cdc_rand_delay_slow_weight=%0d"},
                          prim_cdc_rand_delay_slow_weight));
    void'($value$plusargs({prefix, "prim_cdc_rand_delay_once_weight=%0d"},
                          prim_cdc_rand_delay_once_weight));
    void'($value$plusargs({prefix, "prim_cdc_rand_delay_interval_weight=%0d"},
                          prim_cdc_rand_delay_interval_weight));
    void'($value$plusargs({prefix, "prim_cdc_jitter_ps=%0d"}, prim_cdc_jitter_ps));
    void'($value$plusargs({prefix, "prim_cdc_latency_ps=%0d"}, prim_cdc_latency_ps));

    case (mode)
      "disable":  prim_cdc_rand_delay_mode = RandDelayModeDisable;
      "slow":     prim_cdc_rand_delay_mode = RandDelayModeSlow;
      "once":     prim_cdc_rand_delay_mode = RandDelayModeOnce;
      "interval": prim_cdc_rand_delay_mode = RandDelayModeInterval;
      default:    return 0;
    endcase
    return 1;
  endfunction

  initial begin
    bit res;

    // Command-line override via plusargs (global, applies to ALL instances).
    // Example: +prim_cdc_rand_delay_mode=once
    res = get_plusargs();

    // Command-line override via plusargs (instance-specific).
    // Example: +tb.dut.u_foo.u_bar.u_flop_2sync.u_prim_cdc_rand_delay.prim_cdc_latency_ps=200
    res |= get_plusargs($sformatf("%m"));

    if (!res) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(prim_cdc_rand_delay_mode,
        prim_cdc_rand_delay_mode dist {
          RandDelayModeDisable   :/ prim_cdc_rand_delay_disable_weight,
          RandDelayModeSlow      :/ prim_cdc_rand_delay_slow_weight,
          RandDelayModeOnce      :/ prim_cdc_rand_delay_once_weight,
          RandDelayModeInterval  :/ prim_cdc_rand_delay_interval_weight
        };,
      , $sformatf("%m"))
    end
    update_settings();
  end

  // TODO: Run some performance experiments using this implementation versus an implementation that
  // primarily uses `forever` blocks rather than RTL constructs. Need to also check if this
  // alternate implementation is still valid when compiling/simulating the design.
  if (UseSourceClock) begin : gen_use_source_clock

    // If relying on src_clk, insert a delay on the faster clock.
    always_ff @(posedge src_clk or posedge dst_clk) begin
      src_data_delayed <= src_data;
    end
    assign src_data_with_latency = src_data;

  end else begin : gen_no_use_source_clock

    // If not relying on src_clk, delay by a fixed number of ps determined by the module parameters.
    always @(src_data) begin
      src_data_with_latency <= #(prim_cdc_latency_ps * 1ps) src_data;
    end
    always @(src_data_with_latency) begin
      src_data_delayed <= #(prim_cdc_jitter_ps * 1ps) src_data_with_latency;
    end

  end : gen_no_use_source_clock

  // Randomize delayed random data selection when input data changes, every
  // prim_cdc_rand_delay_interval number of changes.
  int counter = 0;
  always @(src_data_with_latency) begin
    if (mode[RandDelayModeInterval]) begin
      counter <= (counter >= prim_cdc_rand_delay_interval) ? '0 : counter + 1;
      if (counter == prim_cdc_rand_delay_interval) fast_randomize(out_data_mask);
    end else begin
      counter <= 0;
    end
  end

  assign dst_data = mode[RandDelayModeDisable] ? src_data :
                    ((src_data_delayed & out_data_mask) | (src_data_with_latency & ~out_data_mask));

`else

  // Direct pass through.
  assign dst_data = src_data;

`endif  // DISABLE_PRIM_CDC_RAND_DELAY

`else

  // Direct pass through.
  assign dst_data = src_data;

`endif  // SIMULATION

  //TODO: coverage

endmodule
