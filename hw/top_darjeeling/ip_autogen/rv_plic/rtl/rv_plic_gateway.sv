// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RISC-V Platform-Level Interrupt Gateways module

module rv_plic_gateway #(
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

  logic [N_SOURCE-1:0] set;   // Set: (le_i) ? src_i & ~src_q : src_i ;
  logic [N_SOURCE-1:0] src_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) src_q <= '0;
    else         src_q <= src_i;
  end

  always_comb begin
    for (int i = 0 ; i < N_SOURCE; i++) begin
      set[i] = (le_i[i]) ? src_i[i] & ~src_q[i] : src_i[i] ;
    end
  end

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
