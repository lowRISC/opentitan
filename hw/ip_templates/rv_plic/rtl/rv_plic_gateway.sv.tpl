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

  // Interrupt pending is set by source (depends on le_i), cleared by claim_i.
  // Until interrupt is claimed, set doesn't affect ip_o.
  // RISC-V PLIC spec mentioned it can have counter for edge triggered
  // But skipped the feature as counter consumes substantial logic size.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ip_o <= '0;
    end else begin
      ip_o <= (ip_o | (set & ~ia & ~ip_o)) & (~(ip_o & claim_i));
    end
  end

  // Interrupt active is to control ip_o. If ip_o is set then until completed
  // by target, ip_o shouldn't be set by source even claim_i can clear ip_o.
  // ia can be cleared only when ia was set. If `set` and `complete_i` happen
  // at the same time, always `set` wins.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ia <= '0;
    end else begin
      ia <= (ia | (set & ~ia)) & (~(ia & complete_i & ~ip_o));
    end
  end

endmodule
