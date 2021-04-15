// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Mock EDN end point that returns a fixed value after a fixed delay used for
 * OTBN simulation purposes.
 */
module otbn_mock_edn #(
  parameter int Width = 256,
  parameter logic [Width-1:0] FixedEdnVal = '0,
  parameter int Delay = 16,

  localparam int DelayWidth = $clog2(Delay)
) (
  input clk_i,
  input rst_ni,

  input              edn_req_i,
  output             edn_ack_o,
  output [Width-1:0] edn_data_o
);
  parameter int MaxDelay = Delay - 1;
  logic [DelayWidth-1:0] edn_req_counter;
  logic                  edn_req_active;
  logic                  edn_req_complete;

  assign edn_req_complete = edn_req_counter == MaxDelay[DelayWidth-1:0];
  assign edn_ack_o        = edn_req_complete;
  assign edn_data_o       = edn_req_complete ? FixedEdnVal : '0;

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      edn_req_counter <= 0;
      edn_req_active  <= 0;
    end else begin
      if (edn_req_active) begin
        edn_req_counter <= edn_req_counter + 4'b1;
      end

      if (edn_req_i & ~edn_req_active) begin
        edn_req_active <= 1;
      end

      if (edn_req_complete) begin
        edn_req_active <= 0;
      end
    end
  end
endmodule
