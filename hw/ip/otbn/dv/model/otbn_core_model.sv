// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef SYNTHESIS
`include "prim_assert.sv"

/**
 * OpenTitan Big Number Accelerator (OTBN) Core
 *
 * This module is the top-level of the OTBN processing core.
 */

module otbn_core_model
  import otbn_pkg::*;
#(
  // Size of the instruction memory, in bytes
  parameter int ImemSizeByte = 4096,
  // Size of the data memory, in bytes
  parameter int DmemSizeByte = 4096,

  // Scope of the instruction memory (for DPI)
  parameter string ImemScope = "",
  // Scope of the data memory (for DPI)
  parameter string DmemScope = "",
  // Scope of an RTL OTBN implementation (for DPI). If empty, this is a "standalone" model, which
  // should update DMEM on completion. If not empty, we assume it's the scope for the top-level of a
  // real implementation running alongside and we check DMEM contents on completion.
  parameter string DesignScope = "",

  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte)
)(
  input  logic  clk_i,
  input  logic  rst_ni,

  input  logic  start_i, // start the operation
  output bit    done_o,  // operation done

  output err_bits_t err_bits_o, // valid when done_o is asserted

  input  logic [ImemAddrWidth-1:0] start_addr_i, // start byte address in IMEM

  output bit err_o        // something went wrong
);

  import "DPI-C" function chandle otbn_model_init();
  import "DPI-C" function void otbn_model_destroy(chandle handle);
  import "DPI-C" context function
    int unsigned otbn_model_step(chandle           model,
                                 string            imem_scope,
                                 int unsigned      imem_size,
                                 string            dmem_scope,
                                 int unsigned      dmem_size,
                                 string            design_scope,
                                 logic             start_i,
                                 int unsigned      start_addr,
                                 int unsigned      status,
                                 inout bit [31:0]  err_code);

  localparam int ImemSizeWords = ImemSizeByte / 4;
  localparam int DmemSizeWords = DmemSizeByte / (WLEN / 8);

  `ASSERT_INIT(StartAddr32_A, ImemAddrWidth <= 32)
  logic [31:0] start_addr_32;
  assign start_addr_32 = {{32 - ImemAddrWidth{1'b0}}, start_addr_i};

  // Work-around for Verilator. IEEE 1800-2017 says you should compare/assign to a chandle with
  // null. Verilator would prefer you to use zero: it treats null as a synonym of 1'b0 and chandle
  // as a synonym of bit [63:0], so comparing with null causes width mismatch errors.
`ifdef VERILATOR
  chandle chandle_null = 0;
`else
  chandle chandle_null = null;
`endif

  // Create and destroy an object through which we can talk to the ISS.
  chandle model_handle;
  initial begin
    model_handle = otbn_model_init();
    assert(model_handle != chandle_null);
  end
  final begin
    otbn_model_destroy(model_handle);
  end

  // A packed "status" value. This gets assigned by DPI function calls that need to update both
  // whether we're running and also error flags at the same time. The contents are magic simulation
  // values, so get initialized before reset (to avoid stopping the simulation before it even
  // starts).
  int unsigned status = 0;

  // Extract particular bits of the status value.
  //
  //   [0]     running:      The ISS is currently running
  //   [1]     check_due:    The ISS just finished but still needs to check results
  //   [2]     failed_step:  Something went wrong when trying to start or step the ISS.
  //   [3]     failed_cmp:   The consistency check at the end of run failed.

  bit failed_cmp, failed_step, check_due, running;
  assign {failed_cmp, failed_step, check_due, running} = status[3:0];

  bit [31:0] raw_err_bits_d, raw_err_bits_q;
  bit unused_raw_err_bits;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      // Clear status (stop running, and forget any errors)
      status <= 0;
      raw_err_bits_q <= 0;
    end else begin
      if (start_i | running | check_due) begin
        status <= otbn_model_step(model_handle,
                                  ImemScope, ImemSizeWords,
                                  DmemScope, DmemSizeWords,
                                  DesignScope,
                                  start_i, start_addr_32,
                                  status, raw_err_bits_d);
        raw_err_bits_q <= raw_err_bits_d;
      end else begin
        // If we're not running and we're not being told to start, there's nothing to do.
      end
    end
  end

  assign err_bits_o = raw_err_bits_q[7:0];
  assign unused_raw_err_bits = ^raw_err_bits_q[31:8];

  // Track negedges of running_q and expose that as a "done" output.
  bit running_r = 1'b0;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      running_r <= 1'b0;
    end else begin
      running_r <= running;
    end
  end
  assign done_o = running_r & ~running;

  // If DesignScope is not empty, we have a design to check. Bind a copy of otbn_rf_snooper_if into
  // each register file. The otbn_model_check() function will use these to extract memory contents.
  if (DesignScope != "") begin: g_check_design
    // TODO: This bind is by module, rather than by instance, because I couldn't get the by-instance
    // syntax plus upwards name referencing to work with Verilator. Obviously, this won't work with
    // multiple OTBN instances, so it would be nice to get it right.
    bind otbn_rf_base_ff otbn_rf_snooper_if #(.Width (32), .Depth (32)) u_snooper (.rf (rf_reg));
    bind otbn_rf_bignum_ff otbn_rf_snooper_if #(.Width (256), .Depth (32)) u_snooper (.rf (rf));
    bind otbn_rf_base otbn_stack_snooper_if #(.StackWidth (32), .StackDepth(8))
      u_call_stack_snooper (
        .stack_storage(u_call_stack.stack_storage),
        .stack_wr_ptr_q(u_call_stack.stack_wr_ptr_q)
      );
  end

  assign err_o = failed_step | failed_cmp;

endmodule
`endif // SYNTHESIS

