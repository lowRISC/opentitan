// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES SBox testbench

module aes_sbox_tb #(
) (
  input  logic clk_i,
  input  logic rst_ni,

  output logic test_done_o,
  output logic test_passed_o
);

  import aes_pkg::*;

  logic [8:0] count_d, count_q;
  logic [7:0] stimulus;
  ciph_op_e   op;

  localparam int NUM_SBOX_IMPLS = 2;
  localparam int NUM_SBOX_IMPLS_MASKED = 3;
  localparam int NumSBoxImplsTotal = NUM_SBOX_IMPLS + NUM_SBOX_IMPLS_MASKED;
  logic [7:0] responses[NumSBoxImplsTotal];

  // Generate the stimuli
  assign count_d = count_q + 9'h1;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_count
    if (!rst_ni) begin
      count_q <= '0;
    end else if (dom_done) begin
      count_q <= count_d;
    end
  end

  assign op = count_q[8] ? CIPH_FWD : CIPH_INV;
  assign stimulus = count_q[7:0];

  // Instantiate SBox Implementations
  aes_sbox_lut aes_sbox_lut (
    .op_i   ( op           ),
    .data_i ( stimulus     ),
    .data_o ( responses[0] )
  );

  aes_sbox_canright aes_sbox_canright (
    .op_i   ( op           ),
    .data_i ( stimulus     ),
    .data_o ( responses[1] )
  );

  // Mask Generation
  logic  [7:0] masked_stimulus;
  logic  [7:0] in_mask;

  logic  [7:0] masked_response [NUM_SBOX_IMPLS_MASKED];
  logic  [7:0] out_mask [NUM_SBOX_IMPLS_MASKED];

  logic [31:0] mask;
  logic [23:0] unused_mask;

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_mask
    if (!rst_ni) begin
      mask <= 32'hAAFF;
    end else if (dom_done) begin
      mask <= $random;
    end
  end
  assign in_mask     = mask[7:0];
  assign unused_mask = mask[31:8];

  assign masked_stimulus = stimulus ^ in_mask;

  // PRD Generation
  parameter int unsigned WidthPRDSBoxCanrightMasked        = 8;
  parameter int unsigned WidthPRDSBoxCanrightMaskedNoreuse = 18;
  parameter int unsigned WidthPRDSBoxDOM                   = 8;

  logic                                   [31:0] prd;
  logic [31-WidthPRDSBoxCanrightMaskedNoreuse:0] unused_prd;

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_prd
    if (!rst_ni) begin
      prd <= 32'h4321;
    end else begin
      prd <= {$random};
    end
  end
  assign unused_prd = prd[31:WidthPRDSBoxCanrightMaskedNoreuse];

  // Instantiate Masked SBox Implementations
  aes_sbox_canright_masked_noreuse aes_sbox_canright_masked_noreuse (
    .op_i   ( op                                         ),
    .data_i ( masked_stimulus                            ),
    .mask_i ( in_mask                                    ),
    .prd_i  ( prd[WidthPRDSBoxCanrightMaskedNoreuse-1:0] ),
    .data_o ( masked_response[0]                         ),
    .mask_o ( out_mask[0]                                )
  );

  aes_sbox_canright_masked aes_sbox_canright_masked (
    .op_i   ( op                                  ),
    .data_i ( masked_stimulus                     ),
    .mask_i ( in_mask                             ),
    .prd_i  ( prd[WidthPRDSBoxCanrightMasked-1:0] ),
    .data_o ( masked_response[1]                  ),
    .mask_o ( out_mask[1]                         )
  );

  // Instantiate DOM SBox Implementation
  logic dom_done;
  aes_sbox_dom aes_sbox_dom (
    .clk_i     ( clk_i                    ),
    .rst_ni    ( rst_ni                   ),
    .en_i      ( 1'b1                     ),
    .out_req_o ( dom_done                 ),
    .out_ack_i ( 1'b1                     ),
    .op_i      ( op                       ),
    .data_i    ( masked_stimulus          ),
    .mask_i    ( in_mask                  ),
    .prd_i     ( prd[WidthPRDSBoxDOM-1:0] ),
    .data_o    ( masked_response[2]       ),
    .mask_o    ( out_mask[2]              )
  );

  // Unmask responses
  always_comb begin : unmask_resp
    for (int i=0; i<NUM_SBOX_IMPLS_MASKED; i++) begin
      responses[NUM_SBOX_IMPLS+i] = masked_response[i] ^ out_mask[i];
    end
  end

  // Check responses, signal end of simulation
  always_ff @(posedge clk_i or negedge rst_ni) begin : tb_ctrl
    test_done_o   <= 1'b0;
    test_passed_o <= 1'b1;

    for (int i=1; i<NumSBoxImplsTotal; i++) begin
      if (rst_ni && dom_done && (responses[i] != responses[0])) begin
        $display("\nERROR: Mismatch between LUT-based S-Box and Implementation %0d found.", i);
        $display("op = %s, stimulus = 8'h%h, expected resp = 8'h%h, actual resp = 8'h%h\n",
            (op == CIPH_FWD) ? "CIPH_FWD" : "CIPH_INV", stimulus, responses[0], responses[i]);
        test_passed_o <= 1'b0;
        test_done_o   <= 1'b1;
      end
    end

    if (count_q == 9'h1FF) begin
      $display("\nSUCCESS: Outputs of all S-Box implementations match.");
      test_done_o <= 1'b1;
    end
  end

endmodule
