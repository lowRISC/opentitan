// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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

  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte),
  localparam int DmemAddrWidth = prim_util_pkg::vbits(DmemSizeByte)
)(
  input  logic  clk_i,
  input  logic  rst_ni,

  input  logic  start_i, // start the operation
  output logic  done_o,  // operation done

  input  logic [ImemAddrWidth-1:0] start_addr_i // start byte address in IMEM
);


  import "DPI-C" function chandle otbn_model_init();
  import "DPI-C" function void otbn_model_destroy(chandle handle);
  import "DPI-C" context function
    int otbn_model_start(chandle model,
                         string  imem_scope,
                         int     imem_size,
                         string  dmem_scope,
                         int     dmem_size,
                         int     start_addr);
  import "DPI-C" function int otbn_model_step(chandle model);
  import "DPI-C" context function
    int otbn_model_load_dmem(chandle model,
                             string  dmem_scope,
                             int     dmem_size);
  import "DPI-C" context function
    int otbn_model_check(chandle model,
                         string dmem_scope,
                         int    dmem_size,
                         string design_scope);

  chandle model_handle;
  initial begin
    model_handle = otbn_model_init();
    assert(model_handle != 0);
  end
  final begin
    otbn_model_destroy(model_handle);
    model_handle = 0;
  end


  localparam ImemSizeWords = ImemSizeByte / 4;
  localparam DmemSizeWords = DmemSizeByte / (WLEN / 8);

  `ASSERT_INIT(StartAddr32_A, ImemAddrWidth <= 32);
  logic [31:0] start_addr_32;
  assign start_addr_32 = {{32 - ImemAddrWidth{1'b0}}, start_addr_i};

  // The control loop for the model. We track whether we're currently running in the running
  // variable. The step_iss function is run every cycle when not in reset. It steps the ISS if
  // necessary and returns the new value for running.
  function automatic bit step_iss(bit running);
    int retcode;
    bit new_run = running;

    // If start_i is asserted, start again (regardless of whether we're currently running).
    if (start_i) begin
      retcode = otbn_model_start(model_handle,
                                 ImemScope, ImemSizeWords,
                                 DmemScope, DmemSizeWords,
                                 start_addr_32);
      unique case (retcode)
        0:       new_run = 1'b1;
        // Something went wrong. Assume we didn't manage to start.
        default: new_run = 1'b0;
      endcase
    end

    // Otherwise, if we aren't currently running then there's nothing more to do.
    if (!new_run) begin
      return 1'b0;
    end

    // We are running. Step by one instruction.
    retcode = otbn_model_step(model_handle);
    unique case (retcode)
      0: new_run = 1'b1;
      1: begin
        // The model has just finished running. If this is a standalone model (which we can tell
        // because DesignScope is empty), write the ISS's DMEM contents back to the simulation.
        // Otherwise, check the ISS and simulation agree (TODO: We don't do error handling properly
        // at the moment; for now, the C++ code just prints error messages to stderr).
        if (DesignScope.len() == 0) begin
          void'(otbn_model_load_dmem(model_handle, DmemScope, DmemSizeWords));
        end else begin
          void'(otbn_model_check(model_handle, DmemScope, DmemSizeWords, DesignScope));
        end
        new_run = 1'b0;
      end
      // Something went wrong. Assume we've stopped.
      default: new_run = 1'b0;
    endcase
    return new_run;
  endfunction

  bit running, running_r;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      running   <= 1'b0;
      running_r <= 1'b0;
    end else begin
      running   <= step_iss(running);
      running_r <= running;
    end
  end

  // Track negedges of running and expose that as a "done" output.
  assign done_o = running_r & ~running;

  // If DesignScope is not empty, we have a design to check. Bind a copy of otbn_rf_snooper into
  // each register file. The otbn_model_check() function will use these to extract memory contents.
  generate if (DesignScope.len() != 0) begin
    // TODO: This bind is by module, rather than by instance, because I couldn't get the by-instance
    // syntax plus upwards name referencing to work with Verilator. Obviously, this won't work with
    // multiple OTBN instances, so it would be nice to get it right.
    bind otbn_rf_base_ff otbn_rf_snooper #(.Width (32), .Depth (32)) u_snooper (.rf (rf_reg));
    bind otbn_rf_bignum_ff otbn_rf_snooper #(.Width (256), .Depth (32)) u_snooper (.rf (rf));
  end endgenerate

endmodule
