// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// AES Modes of Operation Test Vectors
// https://nvlpubs.nist.gov/nistpubs/legacy/sp/nistspecialpublication800-38a.pdf

// Preamble:
`define AD_LENGTH 0
`define DATA_LENGTH 64
`define NUM_REQUESTS 1922

`define REQUESTS bus_request_t requests[`NUM_REQUESTS] = '{                                         \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-ECB-128 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_ECB,                                                                          \
      key_length: AES_128,                                                                          \
      key:        256'h000000000000000000000000000000003c4fcf098815f7aba6d2ae2816157e2b,            \
      iv:         '0,                                                                               \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_ECB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_ECB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h16157e2b),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'ha6d2ae28),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h8815f7ab),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h3c4fcf09),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CBC-128 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_CBC,                                                                          \
      key_length: AES_128,                                                                          \
      key:        256'h000000000000000000000000000000003c4fcf098815f7aba6d2ae2816157e2b,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CBC) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CBC) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h16157e2b),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'ha6d2ae28),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h8815f7ab),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h3c4fcf09),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CFB-128 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_CFB,                                                                          \
      key_length: AES_128,                                                                          \
      key:        256'h000000000000000000000000000000003c4fcf098815f7aba6d2ae2816157e2b,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h16157e2b),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'ha6d2ae28),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h8815f7ab),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h3c4fcf09),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-OFB-128 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_OFB,                                                                          \
      key_length: AES_128,                                                                          \
      key:        256'h000000000000000000000000000000003c4fcf098815f7aba6d2ae2816157e2b,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_OFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_OFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h16157e2b),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'ha6d2ae28),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h8815f7ab),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h3c4fcf09),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CTR-128 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_CTR,                                                                          \
      key_length: AES_128,                                                                          \
      key:        256'h000000000000000000000000000000003c4fcf098815f7aba6d2ae2816157e2b,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CTR) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CTR) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h16157e2b),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'ha6d2ae28),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h8815f7ab),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h3c4fcf09),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-ECB-128 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_ECB,                                                                          \
      key_length: AES_128,                                                                          \
      key:        256'h000000000000000000000000000000003c4fcf098815f7aba6d2ae2816157e2b,            \
      iv:         '0,                                                                               \
      data:       512'hd45d7204712023823fade8275e780c7b880603ede3001b8823ce8e597fcdb143afbafd965a8985e79d69b90385d5d3f597ef6624f3ca9ea860367a0db47bd73a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_ECB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
 write_request(                                                                                     \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_ECB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h16157e2b),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'ha6d2ae28),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h8815f7ab),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h3c4fcf09),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hb47bd73a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h60367a0d),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hf3ca9ea8),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h97ef6624),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h85d5d3f5),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9d69b903),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h5a8985e7),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hafbafd96),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7fcdb143),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h23ce8e59),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'he3001b88),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h880603ed),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h5e780c7b),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h3fade827),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h71202382),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hd45d7204),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CBC-128 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
 c_dpi_load('{                                                                                      \
      operation:  AES_DEC,                                                                          \
      mode:       AES_CBC,                                                                          \
      key_length: AES_128,                                                                          \
      key:        256'h000000000000000000000000000000003c4fcf098815f7aba6d2ae2816157e2b,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'ha7e1867530ca0e1209ac1f68a1caf13f169522229ee616713b74c1e3b8d6be73b27876913a11db95ee1972509bcb86507d19e9129b8ee9ce46b21981acab4976,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CBC) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CBC) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h16157e2b),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'ha6d2ae28),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h8815f7ab),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h3c4fcf09),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hacab4976),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h46b21981),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h9b8ee9ce),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h7d19e912),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h9bcb8650),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hee197250),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h3a11db95),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hb2787691),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hb8d6be73),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h3b74c1e3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h9ee61671),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h16952222),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'ha1caf13f),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h09ac1f68),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h30ca0e12),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'ha7e18675),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CFB-128 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_CFB,                                                                          \
      key_length: AES_128,                                                                          \
      key:        256'h000000000000000000000000000000003c4fcf098815f7aba6d2ae2816157e2b,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'he6f2f79f6fc6c4ea0e1c5d7c35054bc0dff4a487f18c80b140b1cba3671f75268be51c9fadcde3cd3fa9b3a03745a6c84afb3ce8f849343320ad2db72ed93f3b,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h16157e2b),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'ha6d2ae28),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h8815f7ab),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h3c4fcf09),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h2ed93f3b),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h20ad2db7),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hf8493433),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h4afb3ce8),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h3745a6c8),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h3fa9b3a0),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hadcde3cd),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h8be51c9f),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h671f7526),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h40b1cba3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hf18c80b1),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hdff4a487),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h35054bc0),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h0e1c5d7c),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h6fc6c4ea),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'he6f2f79f),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-OFB-128 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_OFB,                                                                          \
      key_length: AES_128,                                                                          \
      key:        256'h000000000000000000000000000000003c4fcf098815f7aba6d2ae2816157e2b,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h5eaed6c1d910a56678c759f628654c30cced6022a8f74443f6ec5f9c1e05409725d84ec5da523cf5038f91168d5089774afb3ce8f849343320ad2db72ed93f3b,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_OFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_OFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h16157e2b),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'ha6d2ae28),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h8815f7ab),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h3c4fcf09),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h2ed93f3b),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h20ad2db7),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hf8493433),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h4afb3ce8),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h8d508977),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h038f9116),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hda523cf5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h25d84ec5),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h1e054097),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hf6ec5f9c),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'ha8f74443),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hcced6022),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h28654c30),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h78c759f6),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hd910a566),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h5eaed6c1),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CTR-128 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_CTR,                                                                          \
      key_length: AES_128,                                                                          \
      key:        256'h000000000000000000000000000000003c4fcf098815f7aba6d2ae2816157e2b,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'hee9c00f3a0702179d103be2fda1d031eab3eb00d02094f5b5ed3d5db3edfe45afffdffb97b181786fffd70796bf60698ceb60d996468ef1b26e320b691614d87,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CTR) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CTR) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h16157e2b),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'ha6d2ae28),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h8815f7ab),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h3c4fcf09),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h91614d87),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h26e320b6),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h6468ef1b),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hceb60d99),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h6bf60698),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hfffd7079),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b181786),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hfffdffb9),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h3edfe45a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h5ed3d5db),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h02094f5b),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hab3eb00d),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hda1d031e),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hd103be2f),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'ha0702179),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hee9c00f3),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-ECB-192 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_ECB,                                                                          \
      key_length: AES_192,                                                                          \
      key:        256'h00000000000000007b6b2c52d2eaf862e57990802bf310c852640edaf7b0738e,            \
      iv:         '0,                                                                               \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_ECB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_ECB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'hf7b0738e),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'h52640eda),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h2bf310c8),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'he5799080),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'hd2eaf862),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h7b6b2c52),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CBC-192 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_CBC,                                                                          \
      key_length: AES_192,                                                                          \
      key:        256'h00000000000000007b6b2c52d2eaf862e57990802bf310c852640edaf7b0738e,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CBC) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CBC) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'hf7b0738e),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'h52640eda),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h2bf310c8),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'he5799080),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'hd2eaf862),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h7b6b2c52),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CFB-192 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_CFB,                                                                          \
      key_length: AES_192,                                                                          \
      key:        256'h00000000000000007b6b2c52d2eaf862e57990802bf310c852640edaf7b0738e,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'hf7b0738e),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'h52640eda),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h2bf310c8),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'he5799080),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'hd2eaf862),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h7b6b2c52),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-OFB-192 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_OFB,                                                                          \
      key_length: AES_192,                                                                          \
      key:        256'h00000000000000007b6b2c52d2eaf862e57990802bf310c852640edaf7b0738e,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_OFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_OFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'hf7b0738e),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'h52640eda),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h2bf310c8),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'he5799080),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'hd2eaf862),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h7b6b2c52),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CTR-192 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_CTR,                                                                          \
      key_length: AES_192,                                                                          \
      key:        256'h00000000000000007b6b2c52d2eaf862e57990802bf310c852640edaf7b0738e,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CTR) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CTR) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'hf7b0738e),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'h52640eda),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h2bf310c8),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'he5799080),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'hd2eaf862),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h7b6b2c52),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-ECB-192 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_ECB,                                                                          \
      key_length: AES_192,                                                                          \
      key:        256'h00000000000000007b6b2c52d2eaf862e57990802bf310c852640edaf7b0738e,            \
      iv:         '0,                                                                               \
      data:       512'h0e8ec103166916fb726c8d73ba414b9a4e44e6ac2fbae0dc0ae6e27022fd7aefef4eeeecb3ec3477add30a6d84044197cca51f5714a212f75ff2456e1d4f33bd,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_ECB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_ECB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'hf7b0738e),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'h52640eda),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h2bf310c8),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'he5799080),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'hd2eaf862),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h7b6b2c52),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h1d4f33bd),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h5ff2456e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h14a212f7),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hcca51f57),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h84044197),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hadd30a6d),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hb3ec3477),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef4eeeec),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h22fd7aef),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h0ae6e270),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2fbae0dc),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h4e44e6ac),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hba414b9a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h726c8d73),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h166916fb),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h0e8ec103),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CBC-192 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_CBC,                                                                          \
      key_length: AES_192,                                                                          \
      key:        256'h00000000000000007b6b2c52d2eaf862e57990802bf310c852640edaf7b0738e,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'hcd15564fe6a920d98188598879e2b008e002f13dacbaa97fe07afb1220241b575a14693f7638e7e5f4ed7dada9add9b4974104846d0ad3ad7734ecb3ecee4eef,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CBC) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CBC) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'hf7b0738e),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'h52640eda),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h2bf310c8),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'he5799080),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'hd2eaf862),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h7b6b2c52),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hecee4eef),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h7734ecb3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h6d0ad3ad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h97410484),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'ha9add9b4),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hf4ed7dad),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7638e7e5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h5a14693f),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h20241b57),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he07afb12),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hacbaa97f),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'he002f13d),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h79e2b008),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h81885988),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'he6a920d9),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hcd15564f),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CFB-192 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_CFB,                                                                          \
      key_length: AES_192,                                                                          \
      key:        256'h00000000000000007b6b2c52d2eaf862e57990802bf310c852640edaf7b0738e,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'hff094b58ba8fae42a04f83a99c9f5fc0c9c4fa1eed0fe6c8b1889bd51d8a1e2e7a3d1d17702b1a96213617817f7fce6774419ac90959c234ab8cf1dd6f0dc8cd,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'hf7b0738e),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'h52640eda),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h2bf310c8),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'he5799080),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'hd2eaf862),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h7b6b2c52),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h6f0dc8cd),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hab8cf1dd),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h0959c234),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h74419ac9),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7f7fce67),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h21361781),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h702b1a96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h7a3d1d17),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h1d8a1e2e),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hb1889bd5),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hed0fe6c8),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hc9c4fa1e),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h9c9f5fc0),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'ha04f83a9),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hba8fae42),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hff094b58),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-OFB-192 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_OFB,                                                                          \
      key_length: AES_192,                                                                          \
      key:        256'h00000000000000007b6b2c52d2eaf862e57990802bf310c852640edaf7b0738e,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h2ac9acd94b52ac9c3e6cca5708209f6df2a559af4d6d9c556f59f6c0ea9a9a8d010410c10017e8097c83634c8d8bc2fc74419ac90959c234ab8cf1dd6f0dc8cd,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_OFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_OFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'hf7b0738e),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'h52640eda),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h2bf310c8),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'he5799080),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'hd2eaf862),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h7b6b2c52),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h6f0dc8cd),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hab8cf1dd),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h0959c234),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h74419ac9),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h8d8bc2fc),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h7c83634c),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h0017e809),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h010410c1),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hea9a9a8d),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h6f59f6c0),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h4d6d9c55),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hf2a559af),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h08209f6d),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h3e6cca57),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h4b52ac9c),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h2ac9acd9),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CTR-192 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_CTR,                                                                          \
      key_length: AES_192,                                                                          \
      key:        256'h00000000000000007b6b2c52d2eaf862e57990802bf310c852640edaf7b0738e,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h50b0c658ecda975a580998d2f6a7784ff7ab2056661dbdd170c6ebd16bb2361e948ecef4c6c2ccd5effaa60aec3903090b6e7efe59042b4fa21c52172493bc1a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CTR) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_192) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CTR) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'hf7b0738e),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'h52640eda),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h2bf310c8),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'he5799080),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'hd2eaf862),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'h7b6b2c52),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h2493bc1a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'ha21c5217),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h59042b4f),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h0b6e7efe),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hec390309),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'heffaa60a),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hc6c2ccd5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h948ecef4),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h6bb2361e),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h70c6ebd1),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h661dbdd1),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hf7ab2056),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write CT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hf6a7784f),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h580998d2),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hecda975a),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h50b0c658),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read PT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-ECB-256 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_ECB,                                                                          \
      key_length: AES_256,                                                                          \
      key:        256'hf4df1409a310982dd708613b072c351f81777d85f0ae732bbe71ca1510eb3d60,            \
      iv:         '0,                                                                               \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_ECB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_ECB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h10eb3d60),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'hbe71ca15),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'hf0ae732b),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h81777d85),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h072c351f),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'hd708613b),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'ha310982d),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'hf4df1409),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CBC-256 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_CBC,                                                                          \
      key_length: AES_256,                                                                          \
      key:        256'hf4df1409a310982dd708613b072c351f81777d85f0ae732bbe71ca1510eb3d60,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CBC) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CBC) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h10eb3d60),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'hbe71ca15),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'hf0ae732b),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h81777d85),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h072c351f),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'hd708613b),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'ha310982d),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'hf4df1409),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CFB-256 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_CFB,                                                                          \
      key_length: AES_256,                                                                          \
      key:        256'hf4df1409a310982dd708613b072c351f81777d85f0ae732bbe71ca1510eb3d60,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h10eb3d60),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'hbe71ca15),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'hf0ae732b),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h81777d85),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h072c351f),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'hd708613b),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'ha310982d),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'hf4df1409),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-OFB-256 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_OFB,                                                                          \
      key_length: AES_256,                                                                          \
      key:        256'hf4df1409a310982dd708613b072c351f81777d85f0ae732bbe71ca1510eb3d60,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_OFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_OFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h10eb3d60),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'hbe71ca15),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'hf0ae732b),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h81777d85),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h072c351f),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'hd708613b),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'ha310982d),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'hf4df1409),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CTR-256 Encryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_CTR,                                                                          \
      key_length: AES_256,                                                                          \
      key:        256'hf4df1409a310982dd708613b072c351f81777d85f0ae732bbe71ca1510eb3d60,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h10376ce67b412bad179b4fdf45249ff6ef520a1a19c1fbe511e45ca3461cc830518eaf45ac6fb79e9cac031e578a2dae6bc1bee22e409f96e93d7e117393172a,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CTR) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CTR) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h10eb3d60),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'hbe71ca15),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'hf0ae732b),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h81777d85),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h072c351f),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'hd708613b),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'ha310982d),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'hf4df1409),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7393172a),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he93d7e11),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h2e409f96),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h6bc1bee2),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h578a2dae),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9cac031e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hac6fb79e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h518eaf45),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h461cc830),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h11e45ca3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h19c1fbe5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hef520a1a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h45249ff6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h179b4fdf),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b412bad),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h10376ce6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-ECB-256 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_ECB,                                                                          \
      key_length: AES_256,                                                                          \
      key:        256'hf4df1409a310982dd708613b072c351f81777d85f0ae732bbe71ca1510eb3d60,            \
      iv:         '0,                                                                               \
      data:       512'hc7ec249e8f8d7d06fff3f9397a4b30231dedafbeb1e753f1f9f4a69cb921edb6702836314aa75bdc26ed10d410cb1c59f881b13d7e5a4b063ca0d2b5bdd1eef3,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_ECB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_ECB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h10eb3d60),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'hbe71ca15),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'hf0ae732b),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h81777d85),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h072c351f),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'hd708613b),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'ha310982d),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'hf4df1409),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hbdd1eef3),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h3ca0d2b5),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7e5a4b06),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hf881b13d),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h10cb1c59),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h26ed10d4),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h4aa75bdc),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h70283631),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hb921edb6),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hf9f4a69c),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hb1e753f1),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h1dedafbe),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7a4b3023),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hfff3f939),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h8f8d7d06),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hc7ec249e),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CBC-256 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_CBC,                                                                          \
      key_length: AES_256,                                                                          \
      key:        256'hf4df1409a310982dd708613b072c351f81777d85f0ae732bbe71ca1510eb3d60,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h1b9d6a8c07196cdafce99bc3e205ebb26114230463e230a5cfbad9a96933f2397d2c70c67b779f678d80db7e964efc9cd6fb7b5ffbab9e77baf1e5d6044c8cf5,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CBC) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CBC) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h10eb3d60),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'hbe71ca15),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'hf0ae732b),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h81777d85),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h072c351f),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'hd708613b),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'ha310982d),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'hf4df1409),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h044c8cf5),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hbaf1e5d6),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hfbab9e77),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hd6fb7b5f),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h964efc9c),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h8d80db7e),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h7b779f67),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h7d2c70c6),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h6933f239),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hcfbad9a9),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h63e230a5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h61142304),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'he205ebb2),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hfce99bc3),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h07196cda),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h1b9d6a8c),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CFB-256 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_CFB,                                                                          \
      key_length: AES_256,                                                                          \
      key:        256'hf4df1409a310982dd708613b072c351f81777d85f0ae732bbe71ca1510eb3d60,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h71e4b1553d623120f8ceb91a7485a375f9e27a26a8d03ea1924be515241310df7b40e531633c1132c8b1283b14edff3960385d988684cd7e4b1679dabf847edc,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h10eb3d60),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'hbe71ca15),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'hf0ae732b),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h81777d85),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h072c351f),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'hd708613b),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'ha310982d),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'hf4df1409),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hbf847edc),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h4b1679da),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h8684cd7e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h60385d98),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h14edff39),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hc8b1283b),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h633c1132),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h7b40e531),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h241310df),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h924be515),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'ha8d03ea1),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hf9e27a26),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h7485a375),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hf8ceb91a),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h3d623120),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h71e4b155),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-OFB-256 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_OFB,                                                                          \
      key_length: AES_256,                                                                          \
      key:        256'hf4df1409a310982dd708613b072c351f81777d85f0ae732bbe71ca1510eb3d60,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'h84e440e78b5a8f53e87bf3671d14260108c497ba5b1c9df3ed6ee886a047ab718db04f2ad86a8fc83a0bd24067dceb4fdf10132415e54b92a13ed0a8267ae2f9,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_OFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_OFB) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h10eb3d60),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'hbe71ca15),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'hf0ae732b),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h81777d85),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h072c351f),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'hd708613b),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'ha310982d),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'hf4df1409),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h267ae2f9),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'ha13ed0a8),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h15e54b92),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hdf101324),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h67dceb4f),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h3a0bd240),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hd86a8fc8),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h8db04f2a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'ha047ab71),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hed6ee886),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h5b1c9df3),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h08c497ba),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h1d142601),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he87bf367),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h8b5a8f53),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h84e440e7),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /*****************************************************************************/                   \
  /** AES-CTR-256 Decryption                                                  **/                   \
  /*****************************************************************************/                   \
                                                                                                    \
  c_dpi_load('{                                                                                     \
      operation:  AES_DEC,                                                                          \
      mode:       AES_CTR,                                                                          \
      key_length: AES_256,                                                                          \
      key:        256'hf4df1409a310982dd708613b072c351f81777d85f0ae732bbe71ca1510eb3d60,            \
      iv:         128'h0f0e0d0c0b0a09080706050403020100,                                            \
      data:       512'ha641794508ddc213a6ad7ab68dc5c9df8d98842dba1770e84ce93da2da30092bc5f5caca90e984ca9ab5624dcae343f428d2f3bb04f5a7b7a589577713c31e60,\
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers. */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core */                                                                             \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CTR) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_256) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_CTR) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_DEC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h10eb3d60),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'hbe71ca15),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'hf0ae732b),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h81777d85),                                             \
  write_request(AES_KEY_SHARE0_4_OFFSET, 32'h072c351f),                                             \
  write_request(AES_KEY_SHARE0_5_OFFSET, 32'hd708613b),                                             \
  write_request(AES_KEY_SHARE0_6_OFFSET, 32'ha310982d),                                             \
  write_request(AES_KEY_SHARE0_7_OFFSET, 32'hf4df1409),                                             \
  write_request(AES_KEY_SHARE1_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_3_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_4_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_5_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_6_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE1_7_OFFSET, 32'h00000000),                                             \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write IV registers */                                                                          \
  write_request(AES_IV_0_OFFSET, 32'h03020100),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h07060504),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h0b0a0908),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h0f0e0d0c),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 1 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h13c31e60),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'ha5895777),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h04f5a7b7),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h28d2f3bb),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 1 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 2 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hcae343f4),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h9ab5624d),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h90e984ca),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hc5f5caca),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 2 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 3 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'hda30092b),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h4ce93da2),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hba1770e8),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h8d98842d),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 3 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  /* Write PT Block 4 */                                                                            \
  write_request(AES_DATA_IN_0_OFFSET, 32'h8dc5c9df),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'ha6ad7ab6),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h08ddc213),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'ha6417945),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read CT Block 4 */                                                                             \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /* Read VH-specific register */                                                                   \
  read_vh(VH_NAME_0_OFFSET),                                                                        \
  read_vh(VH_VERSION_0_OFFSET)                                                                      \
};
