// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Testbench module for rv_plic. Intended to use with a formal tool.

module rv_plic_assert  #( //TODO: randomize the parameters
  parameter int    N_SOURCE = 55,
  parameter int    N_TARGET = 1,
  parameter int    SRCW     = $clog2(N_SOURCE+1)  // derived parameter
) (
  input clk_i,
  input rst_ni,

  input [N_SOURCE-1:0] intr_src_i,
  input [N_TARGET-1:0] irq_o,
  input [SRCW-1:0]     irq_id_o[N_TARGET],

  input [N_TARGET-1:0] msip_o
);

  logic claim, claimed;
  logic max_priority;
  logic irq;
  logic [SRCW-1:0] i_high_prio;

  // symbolic variables
  int unsigned src_sel;
  int unsigned tgt_sel;

  `ASSUME_FPV(IsrcRange_M, src_sel >= 0 && src_sel < N_SOURCE, clk_i, !rst_ni)
  `ASSUME_FPV(ItgtRange_M, tgt_sel >= 0 && tgt_sel < N_TARGET, clk_i, !rst_ni)
  `ASSUME_FPV(IsrcStable_M, ##1 $stable(src_sel), clk_i, !rst_ni)
  `ASSUME_FPV(ItgtStable_M, ##1 $stable(tgt_sel), clk_i, !rst_ni)

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      claim <= 1'b0;
    end else if (rv_plic.claim[src_sel]) begin
      claim <= 1'b1;
    end else if (rv_plic.complete[src_sel]) begin
      claim <= 1'b0;
    end
  end

  assign claimed = claim || rv_plic.claim[src_sel];

  always_comb begin
    max_priority = 1'b1;
    for (int i = 0; i < N_SOURCE; i++) begin
      // conditions that if src_sel has the highest priority with the lowest ID
      if (i != src_sel && rv_plic.ip[i] && rv_plic.ie[tgt_sel][i] &&
          (rv_plic.prio[i] > rv_plic.prio[src_sel] ||
           (rv_plic.prio[i] == rv_plic.prio[src_sel] && i < src_sel))) begin
        max_priority = 1'b0;
        break;
      end
    end
  end

  always_comb begin
    automatic logic [31:0] max_prio = 0;
    for (int i = N_SOURCE-1; i >= 0; i--) begin
      if (rv_plic.ip[i] && rv_plic.ie[tgt_sel][i] && rv_plic.prio[i] >= max_prio) begin
        max_prio = rv_plic.prio[i];
        i_high_prio = i; // i is the smallest id if have IPs with the same priority
      end
    end
    if (max_prio > rv_plic.threshold[tgt_sel]) irq = 1'b1;
    else irq = 1'b0;
  end

  // when IP is set, previous cycle should follow edge or level triggered criteria
  `ASSERT(LevelTriggeredIp_A, $rose(rv_plic.ip[src_sel]) |->
          $past(rv_plic.le[src_sel]) || $past(intr_src_i[src_sel]), clk_i, !rst_ni)

  `ASSERT(EdgeTriggeredIp_A, $rose(rv_plic.ip[src_sel]) |->
          !$past(rv_plic.le[src_sel]) || $rose($past(intr_src_i[src_sel])), clk_i, !rst_ni)

  // when interrupt is trigger, and nothing claimed yet, then next cycle should assert IP.
  `ASSERT(LevelTriggeredIpWithClaim_A, !rv_plic.le[src_sel] && intr_src_i[src_sel] && !claimed |=>
          rv_plic.ip[src_sel], clk_i, !rst_ni)

  `ASSERT(EdgeTriggeredIpWithClaim_A, rv_plic.le[src_sel] && $rose(intr_src_i[src_sel]) && !claimed |=>
          rv_plic.ip[src_sel], clk_i, !rst_ni)

  // ip stays stable until claimed, reset to 0 after claimed, and stays 0 until complete
  `ASSERT(IpStableAfterTriggered_A, rv_plic.ip[src_sel] && !claimed |=>
          rv_plic.ip[src_sel], clk_i, !rst_ni)
  `ASSERT(IpClearAfterClaim_A, rv_plic.ip[src_sel] && rv_plic.claim[src_sel] |=>
          !rv_plic.ip[src_sel], clk_i, !rst_ni)
  `ASSERT(IpStableAfterClaimed_A, claimed |=> !rv_plic.ip[src_sel], clk_i, !rst_ni)

  // when ip is set and priority is the largest and above threshold, and interrupt enable is set,
  // assertion irq_o at next cycle
  `ASSERT(TriggerIrqForwardCheck_A, rv_plic.ip[src_sel] &&
          rv_plic.prio[src_sel] > rv_plic.threshold[tgt_sel] &&
          max_priority && rv_plic.ie[tgt_sel][src_sel] |=> irq_o[tgt_sel], clk_i, !rst_ni)

  `ASSERT(TriggerIrqBackwardCheck_A, $rose(irq_o[tgt_sel]) |->
          $past(irq) && (irq_id_o[tgt_sel] - 1) == $past(i_high_prio), clk_i, !rst_ni)

  // when irq ID changed, but not to ID=0, irq_o should be high, or irq represents the largest prio
  // but smaller than the threshold
  `ASSERT(IdChangeWithIrq_A, !$stable(irq_id_o[tgt_sel]) && irq_id_o[tgt_sel] != 0 |->
          irq_o[tgt_sel] || ((irq_id_o[tgt_sel] - 1) == $past(i_high_prio) && !$past(irq)),
          clk_i, !rst_ni)
endmodule
