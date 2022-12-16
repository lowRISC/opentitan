// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This module should be instantiated within flops of CDC synchronization primitives,
// and allows DV to model real CDC delays within simulations, especially useful at the chip level
// or in IPs that communicate across clock domains.
//
// The instrumentation is very simple: when this is enabled the input into the first
// synchronizer flop has a mux where the select is randomly set. One of the mux inputs is the input
// of this module, and the other is the output of the first flop: selecting the latter models the
// effect of the first flop missing the input transition.
//
// Notice the delay should cause the input to be skipped by at most a single cycle. As a perhaps
// unnecessary precaution, the select will only be allowed to be random when the input changes.

module prim_cdc_rand_delay #(
    parameter int DataWidth = 1,
    parameter bit Enable = 1
) (
    input logic                   clk_i,
    input logic                   rst_ni,
    input logic [DataWidth-1:0]   prev_data_i,
    input logic [DataWidth-1:0]   src_data_i,
    output logic [DataWidth-1:0]  dst_data_o
);
`ifdef SIMULATION
  if (Enable) begin : gen_enable

    // This controls dst_data_o: any bit with its data_sel set uses prev_data_i, others use
    // src_data_i.
    bit [DataWidth-1:0] data_sel;
    bit                 cdc_instrumentation_enabled;

    function automatic bit [DataWidth-1:0] fast_randomize();
      bit [DataWidth-1:0] data;
      if (DataWidth <= 32) begin
        data = $urandom();
      end else begin
        if (!std::randomize(data)) $fatal(1, "%t: [%m] Failed to randomize data", $time);
      end
      return data;
    endfunction

    initial begin
      void'($value$plusargs("cdc_instrumentation_enabled=%d", cdc_instrumentation_enabled));
      data_sel = '0;
    end

    // Set data_sel at random combinationally when the input changes.
    always @(src_data_i) begin
      data_sel = cdc_instrumentation_enabled ? fast_randomize() : 0;
    end

    // Clear data_del on any cycle start.
    always @(posedge clk_i or negedge rst_ni) begin
      data_sel <= 0;
    end

    always_comb dst_data_o = (prev_data_i & data_sel) | (src_data_i & ~data_sel);
  end else begin : gen_no_enable
    assign dst_data_o = src_data_i;
  end
`else  // SIMULATION
    assign dst_data_o = src_data_i;
`endif  // SIMULATION
endmodule
