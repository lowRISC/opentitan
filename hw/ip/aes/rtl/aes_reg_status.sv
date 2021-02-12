// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES reg status
//
// This module tracks the collective status of multiple registers.

module aes_reg_status import aes_pkg::*;
#(
  parameter int Width = 1
) (
  input  logic             clk_i,
  input  logic             rst_ni,

  input  logic [Width-1:0] we_i,
  input  logic             use_i,
  input  logic             clear_i,
  input  logic             arm_i,
  output sp2v_e            new_o,
  output sp2v_e            clean_o
);

  logic [Width-1:0] we_d, we_q;
  logic             armed_d, armed_q;
  sp2v_e            all_written;
  sp2v_e            none_written;
  sp2v_e            new_d, new_q;
  sp2v_e            clean_d, clean_q;

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
  assign all_written  =  &we_d ? SP2V_HIGH : SP2V_LOW;
  assign none_written = ~|we_d ? SP2V_HIGH : SP2V_LOW;

  // We have a complete new value if all registers have been written at least once.
  assign new_d   = (clear_i || use_i) ? SP2V_LOW : all_written;

  // We have a clean value, if either:
  // - all registers have been written at least once, or
  // - no registers have been written but the value was clean previsously.
  // A value is NOT clean, if either:
  // - we get a clear or reset, or
  // - some but not all registers have been written.
  assign clean_d =  clear_i                    ? SP2V_LOW  :
                   (all_written  == SP2V_HIGH) ? SP2V_HIGH :
                   (none_written == SP2V_HIGH) ? clean_q   : SP2V_LOW;

  // The following primitives are used to place a size-only constraint on the
  // flops in order to prevent optimizations on these status signals.
  logic [Sp2VWidth-1:0] new_q_raw;
  prim_flop #(
    .Width      ( Sp2VWidth            ),
    .ResetValue ( Sp2VWidth'(SP2V_LOW) )
  ) u_new_status_regs (
    .clk_i  ( clk_i     ),
    .rst_ni ( rst_ni    ),
    .d_i    ( new_d     ),
    .q_o    ( new_q_raw )
  );
  assign new_q = sp2v_e'(new_q_raw);

  logic [Sp2VWidth-1:0] clean_q_raw;
  prim_flop #(
    .Width      ( Sp2VWidth            ),
    .ResetValue ( Sp2VWidth'(SP2V_LOW) )
  ) u_clean_status_regs (
    .clk_i  ( clk_i       ),
    .rst_ni ( rst_ni      ),
    .d_i    ( clean_d     ),
    .q_o    ( clean_q_raw )
  );
  assign clean_q = sp2v_e'(clean_q_raw);

  assign new_o   = new_q;
  assign clean_o = clean_q;

endmodule
