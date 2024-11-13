// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module aes_tlul_shim_tb_reqs
  import aes_pkg::*;
  import aes_reg_pkg::*;
  import tlul_pkg::*;
  import aes_tlul_shim_tb_pkg::*;
(
  input logic clk_i,
  input logic rst_ni,

  input logic pop_req_i,

  output shim_request_t req_o,
  //output c_dpi_input_t c_dpi_input_o,
  output logic done_o
);

  int request_cntr_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      request_cntr_q <= 0;
    end else if (pop_req_i) begin
      request_cntr_q <= request_cntr_q + 1;
    end
  end

  always_comb begin
    if (request_cntr_q < `NUM_REQUESTS) begin
      req_o = requests[request_cntr_q];
      //c_dpi_input_o = requests[request_cntr_q].c_dpi_input;
    end else begin
      req_o = '0;
      //c_dpi_input_o = '0;
    end
  end

 assign done_o = (request_cntr_q >= `NUM_REQUESTS) ? 1'b1 : 1'b0;

endmodule
