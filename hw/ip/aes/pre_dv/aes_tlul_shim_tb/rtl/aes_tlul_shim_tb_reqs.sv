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
  output logic done_o
);

  localparam int NumRequests = 54;
  shim_request_t requests[NumRequests];

  initial begin
    requests = '{
      // Check AES core is idle before writing the control registers.
      read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),

      // Config AES core. Config GCM in `INIT` mode.
      write_request(
          AES_CTRL_SHADOWED_OFFSET,
          32'(AES_MANUAL_OPERATION) << AES_CTRL_MANUAL_OPERATION_OFFSET |
          32'(PER_1)                << AES_CTRL_PRNG_RESEED_RATE_OFFSET |
          32'(AES_SIDELOAD)         << AES_CTRL_SIDELOAD_OFFSET         |
          32'(AES_128)              << AES_CTRL_KEY_LEN_OFFSET          |
          32'(AES_GCM)              << AES_CTRL_MODE_OFFSET             |
          32'(AES_ENC)              << AES_CTRL_OPERATION_OFFSET
      ),
      write_request(
          AES_CTRL_SHADOWED_OFFSET,
          32'(AES_MANUAL_OPERATION) << AES_CTRL_MANUAL_OPERATION_OFFSET |
          32'(PER_1)                << AES_CTRL_PRNG_RESEED_RATE_OFFSET |
          32'(AES_SIDELOAD)         << AES_CTRL_SIDELOAD_OFFSET         |
          32'(AES_128)              << AES_CTRL_KEY_LEN_OFFSET          |
          32'(AES_GCM)              << AES_CTRL_MODE_OFFSET             |
          32'(AES_ENC)              << AES_CTRL_OPERATION_OFFSET
      ),
      write_request(
          AES_CTRL_GCM_SHADOWED_OFFSET,
          32'(AES_GCM_NUM_VALID_BYTES) << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |
          32'(GCM_INIT)                << AES_CTRL_GCM_PHASE_OFFSET
      ),
      write_request(
          AES_CTRL_GCM_SHADOWED_OFFSET,
          32'(AES_GCM_NUM_VALID_BYTES) << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |
          32'(GCM_INIT)                << AES_CTRL_GCM_PHASE_OFFSET
      ),
      read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),

      // Write key registers.
      write_request(AES_KEY_SHARE0_0_OFFSET, 32'h03020100),
      write_request(AES_KEY_SHARE0_1_OFFSET, 32'h07060504),
      write_request(AES_KEY_SHARE0_2_OFFSET, 32'h0B0A0908),
      write_request(AES_KEY_SHARE0_3_OFFSET, 32'h0F0E0D0C),
      write_request(AES_KEY_SHARE0_4_OFFSET, 32'h13121110),
      write_request(AES_KEY_SHARE0_5_OFFSET, 32'h17161514),
      write_request(AES_KEY_SHARE0_6_OFFSET, 32'h1B1A1918),
      write_request(AES_KEY_SHARE0_7_OFFSET, 32'h1F1E1D1C),
      write_request(AES_KEY_SHARE1_0_OFFSET, 32'h03020100),
      write_request(AES_KEY_SHARE1_1_OFFSET, 32'h07060504),
      write_request(AES_KEY_SHARE1_2_OFFSET, 32'h0B0A0908),
      write_request(AES_KEY_SHARE1_3_OFFSET, 32'h0F0E0D0C),
      write_request(AES_KEY_SHARE1_4_OFFSET, 32'h13121110),
      write_request(AES_KEY_SHARE1_5_OFFSET, 32'h17161514),
      write_request(AES_KEY_SHARE1_6_OFFSET, 32'h1B1A1918),
      write_request(AES_KEY_SHARE1_7_OFFSET, 32'h1F1E1D1C),
      read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),

      // Write IV registers.
      write_request(AES_IV_0_OFFSET, 32'h00000000),
      write_request(AES_IV_1_OFFSET, 32'h00000000),
      write_request(AES_IV_2_OFFSET, 32'h00000000),
      write_request(AES_IV_3_OFFSET, 32'h00000000),
      read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),

      // Config GCM in `TEXT` mode and write plaintext into the data registers.
      write_request(
          AES_CTRL_GCM_SHADOWED_OFFSET,
          32'(AES_GCM_NUM_VALID_BYTES) << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |
          32'(GCM_TEXT)                << AES_CTRL_GCM_PHASE_OFFSET
      ),
      write_request(
          AES_CTRL_GCM_SHADOWED_OFFSET,
          32'(AES_GCM_NUM_VALID_BYTES) << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |
          32'(GCM_TEXT)                << AES_CTRL_GCM_PHASE_OFFSET
      ),
      read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),

      write_request(AES_DATA_IN_0_OFFSET, 32'h00000000),
      write_request(AES_DATA_IN_1_OFFSET, 32'h00000000),
      write_request(AES_DATA_IN_2_OFFSET, 32'h00000000),
      write_request(AES_DATA_IN_3_OFFSET, 32'h00000000),
      read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),

      // Read out ciphertext
      read_request(AES_DATA_OUT_0_OFFSET),
      read_request(AES_DATA_OUT_1_OFFSET),
      read_request(AES_DATA_OUT_2_OFFSET),
      read_request(AES_DATA_OUT_3_OFFSET),
      read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),

      // Config GCM in `TAG` mode and write len(ad) || len(pt) to trigger tag computation.
      write_request(
          AES_CTRL_GCM_SHADOWED_OFFSET,
          32'(AES_GCM_NUM_VALID_BYTES) << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |
          32'(GCM_TAG)                 << AES_CTRL_GCM_PHASE_OFFSET
      ),
      write_request(
          AES_CTRL_GCM_SHADOWED_OFFSET,
          32'(AES_GCM_NUM_VALID_BYTES) << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |
          32'(GCM_TAG)                 << AES_CTRL_GCM_PHASE_OFFSET
      ),
      write_request(AES_DATA_IN_0_OFFSET, 32'h00000000),
      write_request(AES_DATA_IN_1_OFFSET, 32'h00000000),
      write_request(AES_DATA_IN_2_OFFSET, 32'h00000000),
      write_request(AES_DATA_IN_3_OFFSET, 32'h80000000), // 1 Block
      read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),

      // Read back the authentication tag.
      read_request(AES_DATA_OUT_0_OFFSET),
      read_request(AES_DATA_OUT_1_OFFSET),
      read_request(AES_DATA_OUT_2_OFFSET),
      read_request(AES_DATA_OUT_3_OFFSET),

      // Read Caliptra name and version registers.
      read_request(8'h00,, 1'b1),
      read_request(8'h04,, 1'b1)
    };
  end

  int request_cntr_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      request_cntr_q <= 0;
    end else if (pop_req_i) begin
      request_cntr_q <= request_cntr_q + 1;
    end
  end

  always_comb begin
    if (request_cntr_q < NumRequests) begin
      req_o = requests[request_cntr_q];
    end else begin
      req_o = '0;
    end
  end

  assign done_o = (request_cntr_q >= NumRequests) ? 1'b1 : 1'b0;

endmodule
