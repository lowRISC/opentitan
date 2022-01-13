// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES reg status
//
// This module tracks the collective status of multiple registers.

module aes_reg_status #(
  parameter int Width = 1
) (
  input  logic             clk_i,
  input  logic             rst_ni,

  input  logic [Width-1:0] we_i,
  input  logic             use_i,
  input  logic             clear_i,
  input  logic             arm_i,
  output logic             new_o,
  output logic             new_pulse_o,
  output logic             clean_o
);

  logic [Width-1:0] we_d, we_q;
  logic             armed_d, armed_q;
  logic             all_written;
  logic             none_written;
  logic             new_d, new_q;
  logic             clean_d, clean_q;

  // Collect write operations. Upon clear or use, we start over. If armed, the next write will
  // restart the tracking.
  assign we_d    = (clear_i || use_i) ? '0   :
                   (armed_q && |we_i) ? we_i : (we_q | we_i);
  assign armed_d = (clear_i || use_i) ? 1'b0 :
                   (armed_q && |we_i) ? 1'b0 : armed_q | arm_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_ops
    if (!rst_ni) begin
      we_q    <= '0;
      armed_q <= 1'b0;
    end else begin
      we_q    <= we_d;
      armed_q <= armed_d;
    end
  end

  // Status tracking
  assign all_written  =  &we_d;
  assign none_written = ~|we_d;

  // We have a complete new value if all registers have been written at least once.
  assign new_d   = (clear_i || use_i) ? 1'b0 : all_written;

  // We have a clean value, if either:
  // - all registers have been written at least once, or
  // - no registers have been written but the value was clean previsously.
  // A value is NOT clean, if either:
  // - we get a clear or reset, or
  // - some but not all registers have been written.
  assign clean_d =  clear_i      ? 1'b0    :
                    all_written  ? 1'b1    :
                    none_written ? clean_q : 1'b0;

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_status
    if (!rst_ni) begin
      new_q   <= 1'b0;
      clean_q <= 1'b0;
    end else begin
      new_q   <= new_d;
      clean_q <= clean_d;
    end
  end

  assign new_o       = new_q;
  assign new_pulse_o = new_d & ~new_q;
  assign clean_o     = clean_q;

endmodule
