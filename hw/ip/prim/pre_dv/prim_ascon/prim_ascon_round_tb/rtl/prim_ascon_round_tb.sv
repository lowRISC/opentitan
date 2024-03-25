// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon Permutation testbench

module prim_ascon_round_tb (
  input  logic clk_i,
  input  logic rst_ni,

  output logic test_done_o,
  output logic test_passed_o
);

  import ascon_model_dpi_pkg::*;

  parameter int NUMB_RUNS = 12;
  localparam int ASCON_STATE_WIDTH = 320;

  int count_d, count_q;
  logic [ASCON_STATE_WIDTH-1:0] stimulus;
  logic [ASCON_STATE_WIDTH-1:0] response, response_golden;

  int round;
  assign round = count_q;

  logic [7:0] rcon [12];
  assign rcon[ 0] = 'hf0;
  assign rcon[ 1] = 'he1;
  assign rcon[ 2] = 'hd2;
  assign rcon[ 3] = 'hc3;
  assign rcon[ 4] = 'hb4;
  assign rcon[ 5] = 'ha5;
  assign rcon[ 6] = 'h96;
  assign rcon[ 7] = 'h87;
  assign rcon[ 8] = 'h78;
  assign rcon[ 9] = 'h69;
  assign rcon[10] = 'h5a;
  assign rcon[11] = 'h4b;

  // Generate the stimuli
  assign count_d = count_q + 1;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_count
    if (!rst_ni) begin
      count_q <= 0;
      stimulus <= '0;
    end else begin
      count_q <= count_d;
      stimulus <= {32'hDEADBEEF, 32'hCAFEF00D, 32'hF0F0F0F0,
                   32'hE0E0E0E0, 32'h12345678, 32'h9ABCDEF0,
                   $urandom, $urandom, $urandom, $urandom};
    end
  end

  // Instantiate Ascon Round
  prim_ascon_round ascon_round (
    .state_o (response),
    .state_i (stimulus),
    .rcon_i  (rcon[round])
  );

  always @(stimulus) begin : C_DPI
    c_dpi_ascon_round(stimulus, rcon[round], response_golden);
  end

  initial begin
    test_done_o   = 1'b0;
    test_passed_o = 1'b1;
  end

  // Check responses, signal end of simulation
  always_ff @(posedge clk_i or negedge rst_ni) begin : tb_ctrl
    if (rst_ni && (response_golden != response)) begin
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
