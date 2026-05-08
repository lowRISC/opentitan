// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Non-synthesizable mock EDN end point that returns a fixed value after a fixed
 * delay used for OTBN simulation purposes. This instance is adapted for a 512-bit-
 * wide Bivium PRNG instance requiring 6 times 32-bit words (without coalescing) to seed.
 */
module otbn_mock_edn_bivium
  import edn_pkg::*;
(
  input clk_i,
  input rst_ni,

  input  edn_req_t edn_req_i,
  output edn_rsp_t edn_rsp_o
);

  int   idx_q;
  logic edn_ack_q;

  int values [32'd12] = '{
    32'h99999999,
    32'hAAAAAAAA,
    32'h99999999,
    32'hAAAAAAAA,
    32'h99999999,
    32'hAAAAAAAA,
    32'hBBBBBBBB,
    32'hCCCCCCCC,
    32'hBBBBBBBB,
    32'hCCCCCCCC,
    32'hBBBBBBBB,
    32'hCCCCCCCC
  };

  assign edn_rsp_o.edn_fips = 1'b1;
  assign edn_rsp_o.edn_bus = values[idx_q % 12];
  assign edn_rsp_o.edn_ack = edn_ack_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_idx_increment
    if (!rst_ni) begin
      idx_q <= 32'd0;
    end else if (edn_req_i.edn_req & edn_rsp_o.edn_ack) begin
      idx_q <= idx_q + 32'd1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_gen_ack
    if (!rst_ni) begin
      edn_ack_q <= 1'b0;
    end else if (edn_req_i.edn_req) begin
      edn_ack_q <= !edn_ack_q;
    end
  end

endmodule
