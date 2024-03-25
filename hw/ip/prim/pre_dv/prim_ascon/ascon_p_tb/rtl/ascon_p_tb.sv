// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon Permutation testbench

module ascon_p_tb #(
) (
  input  logic clk_i,
  input  logic rst_ni,

  output logic test_done_o,
  output logic test_passed_o
);

  import ascon_model_dpi_pkg::*;

  parameter int NUMB_RUNS = 10;
  localparam int ASCON_STATE_WIDTH = 320;

  int count_d, count_q;
  logic [ASCON_STATE_WIDTH-1:0] stimulus;
  logic [ASCON_STATE_WIDTH-1:0] response, response_golden;

  // Generate the stimuli
  assign count_d = count_q + 1;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_count
    if (!rst_ni) begin
      count_q <= 0;
      stimulus <= '0;
    end else begin
      count_q <= count_d;
      stimulus <= {{32'hDEADBEEF},{32'hCAFEF00D},{32'hF0F0F0F0},
                   {32'hE0E0E0E0},{32'h12345678},{32'h9ABCDEF0},
                   {$urandom},{$urandom},{$urandom},{$urandom}};
    end
  end

  // Instantiate Ascon Round
  prim_ascon_p ascon_p (
    .state_o   (response),
    .state_i   (stimulus),
    .round_i   (4'b0000),
    .version_i (4'b1100)
  );

  always @(stimulus) begin : C_DPI
    c_dpi_ascon_round(stimulus, 8'hf0, response_golden);
  end


  // Check responses, signal end of simulation
  always_ff @(posedge clk_i or negedge rst_ni) begin : tb_ctrl
    test_done_o   <= 1'b0;
    test_passed_o <= 1'b1;


    if (rst_ni  && (response_golden != response)) begin
      $display("\nERROR: Mismatch between DPI-based Ascon and Implementation found.");
      $display("stimulus      = 320'h%h,\nexpected resp = 320'h%h,\nactual resp   = 320'h%h\n",
         stimulus, response_golden, response);
      test_passed_o <= 1'b0;
      test_done_o   <= 1'b1;

    end

    if (count_q == NUMB_RUNS) begin
      $display("\nSUCCESS: Outputs matches.");
      test_done_o <= 1'b1;
    end
  end

endmodule
