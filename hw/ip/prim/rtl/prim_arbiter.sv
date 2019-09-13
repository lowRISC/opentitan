// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// N:1 arbiter module
//
// verilog parameter
//   N:  Number of request ports
//   DW: Data width
//
// This arbiter implements a first come first serve scheme.
// If the destination is not ready, the current winning request is held until transaction
// is accepted.

module prim_arbiter #(
  parameter N   = 4,
  parameter DW  = 32
) (
  input clk_i,
  input rst_ni,

  input        [ N-1:0] req,
  input        [DW-1:0] req_data [N],
  output logic [ N-1:0] gnt,

  output logic          arb_valid,
  output logic [DW-1:0] arb_data,
  input                 arb_ready
);

  logic [N-1:0] masked_req;
  logic [N-1:0] ppc_out;
  logic [N-1:0] arb_req;

  logic [N-1:0] mask, mask_next;

  logic [N-1:0] winner;

  assign masked_req = mask & req;
  assign arb_req = (|masked_req) ? masked_req : req;

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
  assign gnt    = (arb_ready) ? winner : '0;

  assign arb_valid = |req;
  // Mask Generation
  assign mask_next = {ppc_out[N-2:0], 1'b0};
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mask <= '0;
    end else if (arb_valid && arb_ready) begin
      // Latch only when requests accepted
      mask <= mask_next;
    end else if (arb_valid && !arb_ready) begin
      // Downstream isn't yet ready so, keep current request alive. (First come first serve)
      mask <= ppc_out;
    end
  end

  // ARB DATA
  always_comb begin
    arb_data = '0;
    for (int i = 0 ; i < N ; i++) begin
      if (winner[i]) arb_data = req_data[i];
    end
  end
endmodule
