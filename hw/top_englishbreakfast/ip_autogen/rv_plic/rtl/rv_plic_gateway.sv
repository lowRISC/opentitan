// Copyright lowRISC contributors (OpenTitan project).
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

  // Clear IP and keep it low until `complete_i`. This is non-zero when
  // the CC CSR is read. If no interrupts are pending it will be set to 1,
  // corresponding to the "no interrupt" input.
  //
  // Except for the "no interrupt" value, this must not claim an interrupt
  // that is not pending. This is verified with an assertion.
  input [N_SOURCE-1:0] claim_i, // $onehot0(claim_i)
  // Allow IP to be set again. Ignored for interrupts that aren't already claimed.
  input [N_SOURCE-1:0] complete_i, // $onehot0(complete_i)

  // Interrupt Pending output which is is set when an interrupt is first received.
  // It is cleared and held low when claimed, and then allowed to go high
  // again after completion.
  output logic [N_SOURCE-1:0] ip_o
);

  // True if an interrupt has been claimed so that IP should be held at 0.
  logic [N_SOURCE-1:0] claimed;

  // The set[i] signal says that interrupt i is being requested. If the interrupt is level triggered
  // (because le_i[i]=0) then this just asks that src_i[i] is true. If the interrupt is edge
  // triggered (because le_i[i]=1) then we also ask that src_i[i] was false on the previous cycle
  // (which is registered with src_q).
  logic [N_SOURCE-1:0] set;

  // Registered interrupt input so we can detect edges.
  logic [N_SOURCE-1:0] src_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) src_q <= '0;
    else         src_q <= src_i;
  end

  assign set = src_i & ~(src_q & le_i);

  // "Depending on the design of the device and the interrupt handler, in
  //  between sending an interrupt request and receiving notice of its handler’s completion, the gateway
  //  might either ignore additional matching edges or increment a counter of pending interrupts."
  //
  // This implementation ignores the additional matches as the counters
  // consume substantial logic size.

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ip_o <= '0;
      claimed <= '0;
    end else begin
      // Claim/complete process. It is impossible for a claim and
      // complete to happen in the same cycle because only one CSR access is
      // allowed per cycle. This is verified below.
      claimed <= (claimed | claim_i) & ~complete_i;

      // IP is set if there's an interrupt and cleared if it is claimed.
      // The '| claim_i' is to avoid an extra cycle delay.
      ip_o <= (ip_o | set) & ~(claimed | claim_i);
    end
  end

  // `claim_i` and `complete_i` cannot both be non-zero.
  `ASSERT(NoSimulateneousClaimComplete_A, !(claim_i != '0 && complete_i != '0));

  // We shouldn't see a claim for an interrupt that isn't pending.
  `ASSERT(OnlyClaimPending_A, (claim_i & ~ip_o) == '0);

endmodule
