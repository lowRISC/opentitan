// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RISC-V Platform-Level Interrupt Gateways module

module ${module_instance_name}_gateway #(
  parameter int N_SOURCE = 32
) (
  input clk_i,
  input rst_ni,

  input [N_SOURCE-1:0] src_i,
  input [N_SOURCE-1:0] le_i,      // Level0 Edge1

  input [N_SOURCE-1:0] claim_i, // $onehot0(claim_i)
  input [N_SOURCE-1:0] complete_i, // $onehot0(complete_i)

  output logic [N_SOURCE-1:0] ip_o
);

  logic [N_SOURCE-1:0] ia;    // Interrupt Active

  // The set[i] signal says that interrupt i is being requested. If the interrupt is level triggered
  // (because le_i[i]=0) then this just asks that src_i[i] is true. If the interrupt is edge
  // triggered (because le_i[i]=1) then we also ask that src_i[i] was false on the previous cycle
  // (which is registered with src_q).
  logic [N_SOURCE-1:0] set;
  logic [N_SOURCE-1:0] src_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) src_q <= '0;
    else         src_q <= src_i;
  end

  assign set = src_i & ~(src_q & le_i);

  // The interrupt pending signal for interrupt k stays true until it is claimed (claim_i[k]). It is
  // newly asserted if the interrupt is interrupt asserted (src_i[k]) (restricted to positive edges
  // if le_i[k] is true) when the interrupt isn't already active (~ia[k]).
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ip_o <= '0;
    end else begin
      ip_o <= (ip_o & ~claim_i) | (set & ~ia);
    end
  end

  // The Interrupt Active signal is high for interrupts that are active. Interrupt k becomes active
  // (so ia[k] is true) if the interrupt is asserted when it is not already active. An active
  // interrupt is initially pending (ip_o[k] is high) and stops being pending when claimed by the
  // target setting claim_i[k]. After the interrupt has been claimed, it is marked inactive when the
  // target signals completion (by setting complete_i[k]).
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ia <= '0;
    end else begin
      ia <= (~ia & set) | (ia & ~(complete_i & ~ip_o));
    end
  end

endmodule
