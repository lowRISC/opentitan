// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// N:1 arbiter module
//
// Verilog parameter
//   N:    Number of request ports
//   DW:   Data width
//
// This is the original implementation of the arbiter which relies on parallel prefix
// computing optimization to optimize the request / arbiter tree. Not all synthesis tools
// may support this.
//
// Note that the currently winning request is held if the data sink is not ready.
// This behavior is required by some interconnect protocols (AXI, TL). Note that
// this implies that an asserted request must stay asserted
// until it has been granted. Note that for PPC, this option cannot
// be disabled.
//
// See also: prim_arbiter_tree

`include "prim_assert.sv"

module prim_arbiter_ppc #(
  parameter int unsigned N  = 4,
  parameter int unsigned DW = 32
) (
  input clk_i,
  input rst_ni,

  input        [ N-1:0]        req_i,
  input        [DW-1:0]        data_i [N],
  output logic [ N-1:0]        gnt_o,
  output logic [$clog2(N)-1:0] idx_o,

  output logic          valid_o,
  output logic [DW-1:0] data_o,
  input                 ready_i
);

  `ASSERT_INIT(CheckNGreaterZero_A, N > 0)

  // this case is basically just a bypass
  if (N == 1) begin : gen_degenerate_case

    assign valid_o  = req_i[0];
    assign data_o   = data_i[0];
    assign gnt_o[0] = valid_o & ready_i;
    assign idx_o    = '0;

  end else begin : gen_normal_case

    logic [N-1:0] masked_req;
    logic [N-1:0] ppc_out;
    logic [N-1:0] arb_req;
    logic [N-1:0] mask, mask_next;
    logic [N-1:0] winner;

    assign masked_req = mask & req_i;
    assign arb_req = (|masked_req) ? masked_req : req_i;

    // PPC
    //   Even below code looks O(n) but DC optimizes it to O(log(N))
    //   Using Parallel Prefix Computation
    always_comb begin
      ppc_out[0] = arb_req[0];
      for (int i = 1 ; i < N ; i++) begin
        ppc_out[i] = ppc_out[i-1] | arb_req[i];
      end
    end

    // Grant Generation: Leading-One detector
    assign winner = ppc_out ^ {ppc_out[N-2:0], 1'b0};
    assign gnt_o    = (ready_i) ? winner : '0;

    assign valid_o = |req_i;
    // Mask Generation
    assign mask_next = {ppc_out[N-2:0], 1'b0};
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        mask <= '0;
      end else if (valid_o && ready_i) begin
        // Latch only when requests accepted
        mask <= mask_next;
      end else if (valid_o && !ready_i) begin
        // Downstream isn't yet ready so, keep current request alive. (First come first serve)
        mask <= ppc_out;
      end
    end

    always_comb begin
      data_o = '0;
      idx_o  = '0;
      for (int i = 0 ; i < N ; i++) begin
        if (winner[i]) begin
          data_o = data_i[i];
          idx_o  = i;
        end
      end
    end

  end

  ////////////////
  // assertions //
  ////////////////

  // we can only grant one requestor at a time
  `ASSERT(CheckHotOne_A, $onehot0(gnt_o))
  // A grant implies that the sink is ready
  `ASSERT(GntImpliesReady_A, |gnt_o |-> ready_i)
  // A grant implies that the arbiter asserts valid as well
  `ASSERT(GntImpliesValid_A, |gnt_o |-> valid_o)
  // A request and a sink that is ready imply a grant
  `ASSERT(ReqAndReadyImplyGrant_A, |req_i && ready_i |-> |gnt_o)
  // A request and a sink that is ready imply a grant
  `ASSERT(ReqImpliesValid_A, |req_i |-> valid_o)
  // Both conditions above combined and reversed
  `ASSERT(ReadyAndValidImplyGrant_A, ready_i && valid_o |-> |gnt_o)
  // Both conditions above combined and reversed
  `ASSERT(NoReadyValidNoGrant_A, !(ready_i || valid_o) |-> gnt_o == 0)
  // check index / grant correspond
  `ASSERT(IndexIsCorrect_A, ready_i && valid_o |-> gnt_o[idx_o] && req_i[idx_o])
  // data flow
  `ASSERT(DataFlow_A, ready_i && valid_o |-> data_o == data_i[idx_o])
  // KNOWN assertions on outputs, except for data as that may be partially X in simulation
  // e.g. when used on a BUS
  `ASSERT_KNOWN(ValidKnown_A, valid_o)
  `ASSERT_KNOWN(GrantKnown_A, gnt_o)
  `ASSERT_KNOWN(IdxKnown_A, idx_o)

`ifndef SYNTHESIS
  // A grant implies a request
  int unsigned k; // this is a symbolic variable
  `ASSUME(KStable_M, ##1 $stable(k), clk_i, !rst_ni)
  `ASSUME(KRange_M, k < N, clk_i, !rst_ni)
  `ASSERT(GntImpliesReq_A, gnt_o[k] |-> req_i[k])

  // requests must stay asserted until they have been granted
  `ASSUME(ReqStaysHighUntilGranted_M, (|req_i) && !ready_i |=>
      (req_i & $past(req_i)) == $past(req_i))
  // check that the arbitration decision is held if the sink is not ready
  `ASSERT(LockArbDecision_A, |req_i && !ready_i |=> idx_o == $past(idx_o))

`endif

endmodule
