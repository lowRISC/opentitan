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
// Five (5) different random delay modes are available:
//
// - PrimCdcRandDelayDisable: If this delay mode is picked, this module acts as a simple
//                            passthrough.
//
// - PrimCdcRandDelaySlow: If this delay mode is picked, the output to the dst domain is
//                         continuously driven to `src_data_delayed`.
//
// - PrimCdcRandDelayOnce: If this delay mode is picked, the mask `out_data_mask` used to combine
//                         `src_data_with_latency` and `src_data_delayed` is fully randomized
//                         once at the beginning of the simulation.
//
// - PrimCdcRandDelayInterval: If this delay mode is picked, the mask `out_data_mask` used to
//                            combine `src_data_with_latency` and `src_data_delayed` is fully
//                            randomized every `prim_cdc_num_src_data_changes` times that
//                            `src_data_with_latency` changes.
//
// - PrimCdcRandDelayFull: If this delay mode is picked, the mask `out_data_mask` used to combine
//                         `src_data_with_latency` and `src_data_delayed` is fully randomized
//                         any time `src_data_with_latency` changes.
//
// DV has control of the weights corresponding to each random delay mode when the delay mode is
// randomized, but can also directly override the delay mode as desired.
//
// DV also has control over whether the source clock is used, the latency, and the jitter values -
// these can be modified through the provided setter tasks.

module prim_cdc_rand_delay #(
    parameter int DataWidth = 1,
    parameter bit UseSourceClock = 1,
    parameter int LatencyPs = 500,
    parameter int JitterPs = 500
) (
    input logic                 src_clk,
    input logic [DataWidth-1:0] src_data,

    input logic                   dst_clk,
    output logic [DataWidth-1:0]  dst_data
);

  `ASSERT_INIT(LegalWidth_A, DataWidth > 0)

  int prim_cdc_latency_ps = LatencyPs;
  int prim_cdc_jitter_ps  = JitterPs;

  // Only applies with using CdcRandDelayInterval randomization mode.
  //
  // This is the number of times that `src_data_with_latency` is allowed to change before
  // we re-randomize `out_data_mask`.
  int prim_cdc_num_src_data_changes = 10;
  int counter = 0;

  task automatic set_prim_cdc_latency_ps(int val);
    prim_cdc_latency_ps = val;
    `ASSERT_I(LegalLatency_A, prim_cdc_latency_ps > 0)
  endtask

  task automatic set_prim_cdc_jitter_ps(int val);
    prim_cdc_jitter_ps = val;
    `ASSERT_I(LegalJitter_A, prim_cdc_jitter_ps > 0)
  endtask

  task automatic set_prim_cdc_num_src_data_changes(int val);
    prim_cdc_num_src_data_changes = val;
  endtask

  typedef enum bit [2:0] {
    PrimCdcRandDelayDisable,
    PrimCdcRandDelaySlow,
    PrimCdcRandDelayOnce,
    PrimCdcRandDelayInterval,
    PrimCdcRandDelayFull
  } prim_cdc_rand_delay_mode_e;

  prim_cdc_rand_delay_mode_e prim_cdc_rand_mode;

  logic [DataWidth-1:0] out_data_mask;

  bit en_passthru = 1'b0;

  bit out_randomize_en = 1'b0;

  bit en_rand_interval_mask = 1'b0;

  logic [DataWidth-1:0] src_data_with_latency;
  logic [DataWidth-1:0] src_data_delayed;

  int unsigned prim_cdc_rand_disable_weight  = 0;
  int unsigned prim_cdc_rand_slow_weight     = 20;
  int unsigned prim_cdc_rand_once_weight     = 50;
  int unsigned prim_cdc_rand_interval_weight = 20;
  int unsigned prim_cdc_rand_full_weight     = 10;

  initial begin
    // DV can override these from command line as desired.
    void'($value$plusargs("prim_cdc_latency_ps=%0d",            prim_cdc_latency_ps));
    void'($value$plusargs("prim_cdc_jitter_ps=%0d",             prim_cdc_jitter_ps));
    void'($value$plusargs("prim_cdc_num_src_data_changes=%0d",  prim_cdc_num_src_data_changes));
    void'($value$plusargs("prim_cdc_rand_disable_weight=%0d",   prim_cdc_rand_disable_weight));
    void'($value$plusargs("prim_cdc_rand_slow_weight=%0d",      prim_cdc_rand_slow_weight));
    void'($value$plusargs("prim_cdc_rand_once_weight=%0d",      prim_cdc_rand_once_weight));
    void'($value$plusargs("prim_cdc_rand_interval_weight=%0d",  prim_cdc_rand_interval_weight));
    void'($value$plusargs("prim_cdc_rand_full_weight=%0d",      prim_cdc_rand_full_weight));

    if (!$value$plusargs("prim_cdc_rand_mode=%0d", prim_cdc_rand_mode)) begin
      // By default pick the most performant(*) random delay mode for normal test
      // development/simulation.
      //
      // (*): Need to do some performance experiments to check that the chosen mode is actually the
      //      most performant.
      prim_cdc_rand_mode = PrimCdcRandDelaySlow;
    end

    unique case (prim_cdc_rand_mode)
      PrimCdcRandDelayDisable: begin
        // If CDC randomization disabled, behave like a passthrough
        en_passthru = 1'b1;
      end
      PrimCdcRandDelaySlow: begin
        out_data_mask = '1;
      end
      PrimCdcRandDelayOnce: begin
        void'(std::randomize(out_data_mask));
      end
      PrimCdcRandDelayInterval: begin
        out_randomize_en = 1'b1;
        en_rand_interval_mask = 1'b1;
      end
      PrimCdcRandDelayFull: begin
        out_randomize_en = 1'b1;
      end
      default: begin
        $fatal("%0d is an invalid randomization mode", prim_cdc_rand_mode);
      end
    endcase
  end

  // TODO: Run some performance experiments using this implementation versus an implementation that
  //       primarily uses `forever` blocks rather than RTL constructs.
  //       Need to also check if this alternate implementation is still valid when
  //       compiling/simulating the design.
  if (UseSourceClock) begin : gen_use_source_clock
    // If relying on src_clk, insert a delay on the fastest clock
    always_ff @(posedge src_clk or posedge dst_clk) begin
      src_data_delayed <= src_data;
    end
    assign src_data_with_latency = src_data;
  end else begin : gen_no_use_source_clock
    // If not relying on src_clk, delay by a fixed number of ps determined by the module parameters
    always_comb begin
      src_data_with_latency <= #(prim_cdc_latency_ps * 1ps) src_data;
    end

    always_comb begin
      src_data_delayed <= #(prim_cdc_jitter_ps * 1ps) src_data_with_latency;
    end
  end : gen_no_use_source_clock

  // Randomize delayed random data selection only when input data changes
  always @(src_data_with_latency) begin
    if ((out_randomize_en && !en_rand_interval_mask) ||
        (en_rand_interval_mask && counter == prim_cdc_num_src_data_changes) begin
      for (int i = 0; i < DataWidth; i += 32) begin
        // As of VCS 2017.12-SP2-6, it is slower to randomize for a DataWidth <= 32 with
        // std::randomize() than using $urandom(), which may be more noticeable here as this module
        // can potentially have a large number of instances.
        //
        // Whenever time permits, it will be interesting to run some perf tests with the current VCS
        // version and see what updated performance looks like.
        out_data_mask = (out_data_mask << 32) | $urandom();
      end
    end

    if (en_rand_interval_mask) begin
      counter <= (counter == prim_cdc_num_src_data_changes) ? 0 : counter + 1;
    end
  end

  assign dst_data = (en_passthru) ?
                    (src_data) :
                    ((src_data_delayed & out_data_mask) | (src_data_with_latency & ~out_data_mask));

  //TODO: coverage

endmodule
