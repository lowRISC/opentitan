// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Mock EDN end point that returns a fixed value after a fixed delay used for
 * OTBN simulation purposes.
 */
module otbn_mock_edn
  import edn_pkg::*;
#(
  parameter int Width = 256,
  parameter logic [1:0][Width-1:0] FixedEdnVals = '0,
  parameter int Delay = 16,

  localparam int DelayWidth = $clog2(Delay)
) (
  input clk_i,
  input rst_ni,

  input  edn_req_t edn_req_i,
  output edn_rsp_t edn_rsp_o,

  output [Width-1:0] edn_data_o,
  output             edn_ack_o
);

  assign edn_rsp_o.edn_ack  = edn_req_active && !edn_req_counter[0];
  assign edn_rsp_o.edn_fips = 1'b1;
  assign edn_rsp_o.edn_bus  = edn_req_counter[1] ? 32'hAAAA_AAAA : 32'h9999_9999;

  parameter int MaxDelay = Delay - 1;
  logic                  edn_data_sel_q, edn_data_sel_d;
  logic [DelayWidth-1:0] edn_req_counter;
  logic                  edn_req_active;
  logic                  edn_req_complete;

  assign edn_req_complete = edn_req_counter == MaxDelay[DelayWidth-1:0];
  assign edn_ack_o        = edn_req_complete;
  always_comb begin
    edn_data_o     = '0;
    edn_data_sel_d = edn_data_sel_q;
    if (edn_req_complete) begin
      edn_data_o      = FixedEdnVals[edn_data_sel_q];
      edn_data_sel_d ^= 1'b1; // flip selection of fixed value
    end
  end

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      edn_data_sel_q  <= 1'b0;
      edn_req_counter <= '0;
      edn_req_active  <= 0;
    end else begin
      edn_data_sel_q <= edn_data_sel_d;

      if (edn_req_active) begin
        edn_req_counter <= edn_req_counter + 1;
      end

      if (edn_req_i.edn_req & ~edn_req_active) begin
        edn_req_active <= 1;
      end

      if (edn_req_complete) begin
        edn_req_active <= 0;
      end
    end
  end
endmodule
