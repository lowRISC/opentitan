// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Sink for discarded data DWORDs (Tx Buffers and IBI Queue).
//
// - When transmission fails, the hardware suspends the transmit path and indicates the number of
//   associated DWORDs that still remain in the Tx Buffer.
// - Operation is under control of software and is used as an alternative to flushing the entire
//   queue and starting anew.
// - Operates when 'start' is requested and remains 'active' until all DWORDs consumed.
// - Software may busy wait upon completion because in practice it will take less than
//   50 microseconds and it is used only under the exceptional conditions of transmission failure.

module i3c_data_sink
  import i3c_pkg::*;
#(
  parameter int unsigned NumBuffers = 2,

  // Derived parameters
  localparam int unsigned BufW = $clog2(NumBuffers)
) (
  input                   clk_i,
  input                   rst_ni,

  // Control signals.
  input                   enable_i,
  input                   sw_reset_i,

  // Start request from controlling logic.
  input                   start_i,
  // Properties of the request; static throughout operation.
  input        [BufW-1:0] buf_i,
  input      [BufAddrW:0] dwords_left_i,

  // Reporting of current state.
  output     [BufAddrW:0] dwords_left_o,

  // Activity indication; remains asserted until all DWORDs consumed.
  output                  active_o,
  // Operation failed? e.g. insufficient DWORDs in transmission buffer.
  output                  error_o,

  // Buffer empty indicators.
  input  [NumBuffers-1:0] empty_i,
  // DWORD is available for consumption.
  input  [NumBuffers-1:0] rvalid_i,
  // Normally deasserted, allowing the parent simply to OR them into the FIFO `rready` signals.
  output [NumBuffers-1:0] rready_o
);

  // The maximum number of DWORDs is constrained by the buffer size (currently 4KiB -> 1K DWORDs);
  // allow a couple of bits of headroom in case the message buffer is enlarged later.
  logic [BufAddrW:0] dwords_left;

  // Select the appropriate input signals; software shall not change `buf_i` whilst active.
  logic [BufW-1:0] valid;
  assign valid = rvalid_i >> buf_i;
  logic [BufW-1:0] empty;
  assign empty = empty_i >> buf_i;

  // Error indicator is sticky until the next operation or reset.
  logic error;

  // This logic just consumes a number of words of data from a queue when requested.
  wire active = |dwords_left;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dwords_left <= 'b0;
      error       <= 1'b0;
    end else if (sw_reset_i) begin
      dwords_left <= 'b0;
      error       <= 1'b0;
    end else if (enable_i) begin
      if (start_i) begin
        dwords_left <= dwords_left_i;
        error       <= 1'b0;
      end else if (active) begin
        if (valid[0]) dwords_left <= dwords_left - 1'b1;
        else if (empty[0]) begin
          error       <= 1'b1;
          dwords_left <= 'b0;   // Become inactive.
        end
      end
    end
  end

  // Activity indicator.
  assign active_o = active;
  assign error_o  = error;

  // Status information.
  assign dwords_left_o = dwords_left;

  // Consume DWORDs as fast as the queue allows.
  assign rready_o = NumBuffers'(active) << buf_i;

endmodule
