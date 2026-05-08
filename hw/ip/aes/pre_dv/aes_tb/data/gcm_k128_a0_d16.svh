// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// AES-GCM-128 Test Case #2
// https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf

// Preamble:
`define AD_LENGTH 0
`define DATA_LENGTH 16
`define NUM_REQUESTS 54

`define REQUESTS bus_request_t requests[`NUM_REQUESTS] = '{                                         \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_GCM,                                                                          \
      key_length: AES_128,                                                                          \
      key:        256'h0000000000000000000000000000000000000000000000000000000000000000,            \
      iv:         128'h0000000000000000000000000000000000,                                          \
      data:       128'h0000000000000000000000000000000000,                                          \
      ad:         '0,                                                                               \
      tag:        '0                                                                                \
  }),                                                                                               \
                                                                                                    \
  /* Check AES core is idle before writing the control registers  */                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config AES core, config GCM in `INIT` mode */                                                  \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_GCM) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_SHADOWED_OFFSET,                                                                     \
      32'(0)       << AES_CTRL_MANUAL_OPERATION_OFFSET |                                            \
      32'(PER_1)   << AES_CTRL_PRNG_RESEED_RATE_OFFSET |                                            \
      32'(0)       << AES_CTRL_SIDELOAD_OFFSET         |                                            \
      32'(AES_128) << AES_CTRL_KEY_LEN_OFFSET          |                                            \
      32'(AES_GCM) << AES_CTRL_MODE_OFFSET             |                                            \
      32'(AES_ENC) << AES_CTRL_OPERATION_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_GCM_SHADOWED_OFFSET,                                                                 \
      32'(16)       << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |                                        \
      32'(GCM_INIT) << AES_CTRL_GCM_PHASE_OFFSET                                                    \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_GCM_SHADOWED_OFFSET,                                                                 \
      32'(16)       << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |                                        \
      32'(GCM_INIT) << AES_CTRL_GCM_PHASE_OFFSET                                                    \
  ),                                                                                                \
                                                                                                    \
  /* Write key registers.*/                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h00000000),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h00000000),                                             \
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
  write_request(AES_IV_0_OFFSET, 32'h00000000),                                                     \
  write_request(AES_IV_1_OFFSET, 32'h00000000),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h00000000),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h00000000),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config GCM in `TEXT` mode and write plaintext block 1 into the data registers */               \
  write_request(                                                                                    \
      AES_CTRL_GCM_SHADOWED_OFFSET,                                                                 \
      32'(16)       << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |                                        \
      32'(GCM_TEXT) << AES_CTRL_GCM_PHASE_OFFSET                                                    \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_GCM_SHADOWED_OFFSET,                                                                 \
      32'(16)       << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |                                        \
      32'(GCM_TEXT) << AES_CTRL_GCM_PHASE_OFFSET                                                    \
  ),                                                                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_INPUT_READY_OFFSET),                      \
                                                                                                    \
  write_request(AES_DATA_IN_0_OFFSET, 32'h00000000),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h00000000),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h00000000),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h00000000),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read out ciphertext */                                                                         \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config GCM in `TAG` mode and write len(ad) || len(pt) to trigger tag computation */            \
  write_request(                                                                                    \
      AES_CTRL_GCM_SHADOWED_OFFSET,                                                                 \
      32'(16)      << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |                                         \
      32'(GCM_TAG) << AES_CTRL_GCM_PHASE_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_GCM_SHADOWED_OFFSET,                                                                 \
      32'(16)      << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |                                         \
      32'(GCM_TAG) << AES_CTRL_GCM_PHASE_OFFSET                                                     \
  ),                                                                                                \
  write_request(AES_DATA_IN_0_OFFSET, 32'h00000000),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h00000000),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h00000000),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h80000000),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read back the authentication tag */                                                            \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
                                                                                                    \
  /* Read VH-specific register */                                                                   \
  read_vh(VH_NAME_0_OFFSET),                                                                        \
  read_vh(VH_VERSION_0_OFFSET)                                                                      \
};
