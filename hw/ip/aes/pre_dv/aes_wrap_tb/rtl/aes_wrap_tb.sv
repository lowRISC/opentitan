// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES SBox testbench

module aes_wrap_tb #(
) (
  input  logic clk_i,
  input  logic rst_ni,

  output logic test_done_o,
  output logic test_passed_o
);

  logic [127:0] aes_output;
  logic         test_done;
  logic   [7:0] count_d, count_q;

  // Instantiate DUT
  aes_wrap aes_wrap (
    .clk_i,
    .rst_ni,

    .aes_input   ( 128'h0     ),
    .aes_key     ( 256'h0     ),
    .aes_output  ( aes_output ),

    .test_done_o ( test_done  )
  );

  // Count the time.
  assign count_d = count_q + 8'h1;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_count
    if (!rst_ni) begin
      count_q <= '0;
    end else begin
      count_q <= count_d;
    end
  end

  // Check responses, signal end of simulation
  always_ff @(posedge clk_i or negedge rst_ni) begin : tb_ctrl
    test_done_o   <= 1'b0;
    test_passed_o <= 1'b0;

    if (rst_ni && test_done) begin
      if (aes_output == 128'h2e2b34ca59fa4c883b2c8aefd44be966) begin
        $display("\nSUCCESS: AES output matches expected value.");
        test_passed_o <= 1'b1;
        test_done_o   <= 1'b1;
      end else begin
        $display("\nERROR: AES output does not match expected value.");
        test_passed_o <= 1'b0;
        test_done_o   <= 1'b1;
      end
    end

    if (count_q == 8'hFF) begin
      $display("\nERROR: Simulation timed out.");
      test_done_o <= 1'b1;
    end
  end

endmodule
