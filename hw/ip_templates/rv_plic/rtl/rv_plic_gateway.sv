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

  // Incoming interrupt requests from the interrupt sources.
  input [N_SOURCE-1:0] src_i,

  // Control whether each interrupt is level or edge triggered. It is considered level triggered if
  // its bit of le_i is zero and edge triggered if the bit is 1.
  input [N_SOURCE-1:0] le_i,

  // Interrupts being claimed by a target. This should be onehot0 (so only one interrupt can be
  // claimed at once).
  input [N_SOURCE-1:0] claim_i,

  // Interrupts being marked complete by a target. This should be onehot0 (so only one interrupt can
  // be claimed at once). It has no effect on an interrupt that has not already been claimed.
  input [N_SOURCE-1:0] complete_i,

  // The "interrupt pending" flag. If a bit of ip_o is true, the target should be notified that the
  // interrupt needs handling.
  output logic [N_SOURCE-1:0] ip_o
);

  // The flow for an interrupt is described in "RISC-V Platform-Level Interrupt Controller
  // Specification" (v1.0.0) in section 1.5.
  //
  //   1. An interrupt starts neither active nor pending (so the relevant bits of ia and ip_o are
  //      zero).
  //
  //   2. The interrupt source asserts interrupt k by setting src_i[k]. If le_i requests edge
  //      triggering, the gateway only recognises an interrupt with a posedge on src_i.
  //
  //   3. The gateway sets ip_o[k] to tell the target that interrupt k is pending.
  //
  //   4. The target claims the interrupt, which appears as claim_i[k] being true.
  //
  //   5. The gateway clears ip_o[k], but remembers that the interrupt is being handled. As such,
  //      further changes in src_i will not cause a new (overlapping) interrupt.
  //
  //   6. The target finishes handling the interrupt and sets complete_i[k].
  //
  //   7. The gateway will now allow changes in src_i to cause the interrupt to become pending
  //      again.
  //
  // This is translated into hardware signals as follows:
  //
  //   - The interrupt assertion in src_i is detected with the "set" signal. This includes posedge
  //     detection if le_i is true for the interrupt.
  //
  //   - Once interrupt k is asserted, it is marked pending in ip_o[k]. It is also marked "active"
  //     (which implies the target hasn't yet got as far as completion) by setting ia[k].
  //
  //   - When the target claims the interrupt, ip_o[k] is cleared, but ia[k] stays high.
  //
  //   - Finally, when the target completes the interrupt, ia[k] is cleared.

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

  // Check the claim_i and complete_i input ports are being driven with onehot0 values.
  `ASSERT(ClaimOneHot0_A,    $onehot0(claim_i))
  `ASSERT(CompleteOneHot0_A, $onehot0(complete_i))

endmodule
