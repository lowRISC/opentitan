// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Testbench module for rv_plic. Intended to use with a formal tool.

module rv_plic_assert  #( //TODO: randomize the parameters
  parameter int    N_SOURCE = 54,
  parameter int    N_TARGET = 1,
  parameter string FIND_MAX = "SEQUENTIAL", // SEQUENTIAL | MATRIX

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
  int unsigned i_src;
  int unsigned i_tgt;

  `ASSUME_FPV(IsrcRange_M, i_src >= 0 && i_src < N_SOURCE, clk_i, !rst_ni)
  `ASSUME_FPV(ItgtRange_M, i_tgt >= 0 && i_tgt < N_TARGET, clk_i, !rst_ni)
  `ASSUME_FPV(IsrcStable_M, ##1 $stable(i_src), clk_i, !rst_ni)
  `ASSUME_FPV(ItgtStable_M, ##1 $stable(i_tgt), clk_i, !rst_ni)

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      claim <= 1'b0;
    end else if (rv_plic.claim[i_src]) begin
      claim <= 1'b1;
    end else if (rv_plic.complete[i_src]) begin
      claim <= 1'b0;
    end
  end

  assign claimed = claim || rv_plic.claim[i_src];

  always_comb begin
    max_priority = 1'b1;
    for (int i = 0; i < N_SOURCE; i++) begin
      // conditions that if i_src has the highest priority with the lowest ID
      if (i != i_src && rv_plic.ip[i] && rv_plic.ie[i_tgt][i] &&
          (rv_plic.prio[i] > rv_plic.prio[i_src] ||
           (rv_plic.prio[i] == rv_plic.prio[i_src] && i < i_src))) begin
        max_priority = 1'b0;
        break;
      end
    end
  end

  always_comb begin
    automatic logic [31:0] max_prio = rv_plic.threshold[i_tgt];
    for (int i = 0; i < N_SOURCE; i++) begin
      if (rv_plic.ip[i] && rv_plic.ie[i_tgt][i] && rv_plic.prio[i] > max_prio) begin
        max_prio = rv_plic.prio[i];
        i_high_prio = i; // i is the smallest id if have IPs with the same priority
      end
    end
    if (max_prio > rv_plic.threshold[i_tgt]) irq = 1'b1;
  end

  // when IP is set, previous cycle should follow edge or level triggered criteria
  `ASSERT(LevelTriggeredIp_A, $rose(rv_plic.ip[i_src]) |->
          $past(rv_plic.le[i_src]) || $past(intr_src_i[i_src]), clk_i, !rst_ni)

  `ASSERT(EdgeTriggeredIp_A, $rose(rv_plic.ip[i_src]) |->
          !$past(rv_plic.le[i_src]) || $rose($past(intr_src_i[i_src])), clk_i, !rst_ni)

  // when interrupt is trigger, and nothing claimed yet, then next cycle should assert IP.
  `ASSERT(LevelTriggeredIpWithClaim_A, !rv_plic.le[i_src] && intr_src_i[i_src] && !claimed |=>
          rv_plic.ip[i_src], clk_i, !rst_ni)

  `ASSERT(EdgeTriggeredIpWithClaim_A, rv_plic.le[i_src] && $rose(intr_src_i[i_src]) && !claimed |=>
          rv_plic.ip[i_src], clk_i, !rst_ni)

  // ip stays stable until claimed, reset to 0 after claimed, and stays 0 until complete
  `ASSERT(IpStableAfterTriggered_A, rv_plic.ip[i_src] && !claimed |=>
          rv_plic.ip[i_src], clk_i, !rst_ni)
  `ASSERT(IpClearAfterClaim_A, rv_plic.ip[i_src] && rv_plic.claim[i_src] |=>
          !rv_plic.ip[i_src], clk_i, !rst_ni)
  `ASSERT(IpStableAfterClaimed_A, claimed |=> !rv_plic.ip[i_src], clk_i, !rst_ni) // state based

  // when ip is set and priority is the largest and above threshold, and interrupt enable is set,
  // assertion irq_o at next cycle
  `ASSERT(TriggerIrqForwardCheck_A, rv_plic.ip[i_src] &&
          rv_plic.prio[i_src] > rv_plic.threshold[i_tgt] &&
          max_priority && rv_plic.ie[i_tgt][i_src]
          |=> irq_o[i_tgt] && irq_id_o[i_tgt] == SRCW'(i_src + 1), clk_i, !rst_ni)

  `ASSERT(TriggerIrqBackwardCheck_A, $rose(irq_o[i_tgt]) |->
          $past(irq) && (irq_id_o[i_tgt] - 1) == $past(i_high_prio), clk_i, !rst_ni)

  // when irq ID changed, but not to ID=0, irq_o should be high
  `ASSERT(IdChangeWithIrq_A, !$stable(irq_id_o[i_tgt]) && irq_id_o[i_tgt] != 0 |->
          irq_o[i_tgt], clk_i, !rst_ni)
endmodule
