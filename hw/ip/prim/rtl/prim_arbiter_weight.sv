// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// N:1 Weighted Round-Robin arbiter module
//
// Verilog parameter
//   N:             Number of request ports
//   DW:            Data width
//   EnDataPort:    Set to 1 to enable the data port.
//   MaxWeight:     Maximum Weight Value
//
// This module implements the weighted round-robin (WRR) arbiter scheme.
//
// WRR can be implemented in two ways. One is to consume a request fully then
// move on to the next request. Other way is to consume RR way then re-visit.
// This module implements the second.

`include "prim_assert.sv"

module prim_arbiter_weight #(
  parameter int unsigned N  = 8,
  parameter int unsigned DW = 32,

  // Configurations
  // EnDataPort: {0, 1}, if 0, input data will be ignored
  parameter bit EnDataPort = 1'b 1,

  parameter int unsigned MaxWeight = 7,

  // Derived parameters
  localparam int IdxW    = $clog2(N),
  localparam int WeightW = $clog2(MaxWeight+1)
) (
  input clk_i,
  input rst_ni,

  input        [   N-1:0] req_i,
  input        [  DW-1:0] data_i [N],
  output logic [   N-1:0] gnt_o,
  output logic [IdxW-1:0] idx_o,

  output logic            valid_o,
  output logic [  DW-1:0] data_o,
  input                   ready_i,

  // Configuration (Weight)
  input [N-1:0][WeightW-1:0] weight_i
);

  `ASSERT_INIT(CheckNGreaterThanOne_A, N > 1)

  logic [N-1:0] masked_req, arb_req;
  logic [N-1:0] mask, mask_d;
  logic [N-1:0] winner;

  logic [N-1:0][WeightW-1:0] cur_weight;

  assign masked_req = mask & req_i;
  assign arb_req    = (|masked_req) ? masked_req : req_i;

  // Current Weight
  //
  //   Weight is reset to the given value `weight_i` when all cur_weight[i] &
  //   req[i] are 0. The logic reduces the weight[i] when the logic grants the
  //   req[i].
  logic [N-1:0] pending_weight_nonzero;
  logic         reset_weight;
  always_comb begin
    for (int unsigned i = 0 ; i < N ; i++) begin
      pending_weight_nonzero[i] = (req_i[i]) ? |cur_weight[i] : 1'b 0;
    end
  end

  // reset_weight remains high if |req_i[i] is 0 (no requests).
  assign reset_weight = ~|pending_weight_nonzero;

  for (genvar i = 0 ; i < N ; i++) begin : g_cur_weight
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) cur_weight[i] <= '0;
      else begin
        unique case ({reset_weight, gnt_o[i]})
          2'b 00: cur_weight[i] <= cur_weight[i];
          2'b 01: cur_weight[i] <= cur_weight[i] - 1'b 1;
          2'b 10: cur_weight[i] <= weight_i[i];
          2'b 11: cur_weight[i] <= weight_i[i] - 1'b 1;

          default: cur_weight[i] <= cur_weight[i];
        endcase
      end
    end
  end

  // Masking
  logic [N-1:0] ppc_out;
  always_comb begin
    ppc_out[0] = arb_req[0];
    for (int i = 1 ; i < N ; i++) begin
      ppc_out[i] = ppc_out[i-1] | arb_req[i];
    end
  end

  assign mask_d = {ppc_out[N-2:0], 1'b 0} & pending_weight_nonzero;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) mask <= '0;
    else if (valid_o && ready_i)  mask <= mask_d ;
    else if (valid_o && !ready_i) mask <= ppc_out;
  end

  assign winner = ppc_out ^ {ppc_out[N-2:0], 1'b 0};
  assign gnt_o  = (ready_i) ? winner : '0;

  assign valid_o = |req_i;

  if (EnDataPort == 1) begin: gen_datapath
    always_comb begin
      data_o = '0;
      for (int i = 0 ; i < N ; i++) begin
        if (winner[i]) begin
          data_o = data_i[i];
        end
      end
    end
  end else begin: gen_nodatapath
    assign data_o = '1;
    // The following signal is used to avoid possible lint errors.
    logic [DW-1:0] unused_data [N];
    assign unused_data = data_i;
  end

  always_comb begin
    idx_o = '0;
    for (int unsigned i = 0 ; i < N ; i++) begin
      if (winner[i]) begin
        idx_o = i[IdxW-1:0];
      end
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // KNOWN assertions on outputs, except for data as that may be partially X in
  // simulation.
  // e.g. when used on a BUS
  `ASSERT_KNOWN(ValidKnown_A, valid_o)
  `ASSERT_KNOWN(GrantKnown_A, gnt_o)
  `ASSERT_KNOWN(IdxKnown_A,   idx_o)

  // we can only grant one requestor at a time
  `ASSERT(CheckHotOne_A, $onehot0(gnt_o))
  // A grant implies that the sink is ready
  `ASSERT(GntImpliesReady_A, |gnt_o |-> ready_i)
  // A grant implies that the arbiter asserts valid as well
  `ASSERT(GntImpliesValid_A, |gnt_o |-> valid_o)
  // A request and a sink that is ready imply a grant. No cycle gap.
  `ASSERT(ReqAndReadyImplyGrant_A, |req_i && ready_i |-> |gnt_o)
  // A request and a sink that is ready imply a grant
  `ASSERT(ReqImpliesValid_A, |req_i |-> valid_o)
  // Both conditions above combined and reversed
  `ASSERT(ReadyAndValidImplyGrant_A, ready_i && valid_o |-> |gnt_o)
  // Both conditions above combined and reversed
  `ASSERT(NoReadyValidNoGrant_A, !(ready_i || valid_o) |-> gnt_o == 0)
  // check index / grant correspond
  `ASSERT(IndexIsCorrect_A, ready_i && valid_o |-> gnt_o[idx_o] && req_i[idx_o])
  if (EnDataPort) begin: gen_data_port_assertion
    // data flow
    `ASSERT(DataFlow_A, ready_i && valid_o |-> data_o == data_i[idx_o])
  end

  // requests must stay asserted until they have been granted
  `ASSUME(ReqStaysHighUntilGranted0_M, |req_i && !ready_i |=>
      (req_i & $past(req_i)) == $past(req_i), clk_i, !rst_ni)
  // check that the arbitration decision is held if the sink is not ready
  `ASSERT(LockArbDecision_A, |req_i && !ready_i |=> idx_o == $past(idx_o),
      clk_i, !rst_ni)

  for (genvar i = 0 ; i < N ; i++) begin : g_assert_chk_weight_i
    // When valid goes out, the weight should be greater than or equal to 1.
    `ASSUME(WeightInputGTZero_A, req_i[i] |-> weight_i[i] != 0)

    // When logic resets the current weights, it can grant.
    `ASSERT(NotUnderflow_A, gnt_o[i] & !reset_weight |-> cur_weight[i] != '0)
  end

endmodule : prim_arbiter_weight
