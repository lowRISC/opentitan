// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// AES-GCM-128 Test Case #3
// https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf

// Preamble:
`define AD_LENGTH 20
`define DATA_LENGTH 64
`define NUM_REQUESTS 110

`define REQUESTS bus_request_t requests[`NUM_REQUESTS] = '{                                         \
  c_dpi_load('{                                                                                     \
      operation:  AES_ENC,                                                                          \
      mode:       AES_GCM,                                                                          \
      key_length: AES_128,                                                                          \
      key:        256'h0000000000000000000000000000000008833067948f6a6d1c73658692e9fffe,            \
      iv:         128'h0000000088f8cadeaddbcefabebafeca,                                            \
      data:       512'h55d2af1a397b63ba57e60daaf5ed6ab125b5a649240ecf2f53096895950c3c1c728a318a3d304c2edaf7341553a9a7869a26f5afc50959a5e50684f8253231d9,\
      ad:         160'hd2daadabefbeaddecefaedfeefbeaddecefaedfe,                                    \
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
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Write key registers */                                                                         \
  write_request(AES_KEY_SHARE0_0_OFFSET, 32'h92e9fffe),                                             \
  write_request(AES_KEY_SHARE0_1_OFFSET, 32'h1c736586),                                             \
  write_request(AES_KEY_SHARE0_2_OFFSET, 32'h948f6a6d),                                             \
  write_request(AES_KEY_SHARE0_3_OFFSET, 32'h08833067),                                             \
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
  write_request(AES_IV_0_OFFSET, 32'hbebafeca),                                                     \
  write_request(AES_IV_1_OFFSET, 32'haddbcefa),                                                     \
  write_request(AES_IV_2_OFFSET, 32'h88f8cade),                                                     \
  write_request(AES_IV_3_OFFSET, 32'h00000000),                                                     \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config GCM in `AAD` mode and write AD block 1 into the data registers */                       \
  write_request(                                                                                    \
      AES_CTRL_GCM_SHADOWED_OFFSET,                                                                 \
      32'(16)      << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |                                         \
      32'(GCM_AAD) << AES_CTRL_GCM_PHASE_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_GCM_SHADOWED_OFFSET,                                                                 \
      32'(16)      << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |                                         \
      32'(GCM_AAD) << AES_CTRL_GCM_PHASE_OFFSET                                                     \
  ),                                                                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  write_request(AES_DATA_IN_0_OFFSET, 32'hcefaedfe),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hefbeadde),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hcefaedfe),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'hefbeadde),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config GCM in `AAD` mode and write AD block 2 into the data registers */                       \
  write_request(                                                                                    \
      AES_CTRL_GCM_SHADOWED_OFFSET,                                                                 \
      32'(4)       << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |                                         \
      32'(GCM_AAD) << AES_CTRL_GCM_PHASE_OFFSET                                                     \
  ),                                                                                                \
  write_request(                                                                                    \
      AES_CTRL_GCM_SHADOWED_OFFSET,                                                                 \
      32'(4)       << AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET |                                         \
      32'(GCM_AAD) << AES_CTRL_GCM_PHASE_OFFSET                                                     \
  ),                                                                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  write_request(AES_DATA_IN_0_OFFSET, 32'hd2daadab),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h00000000),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h00000000),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h00000000),                                                \
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
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  write_request(AES_DATA_IN_0_OFFSET, 32'h253231d9),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'he50684f8),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'hc50959a5),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h9a26f5af),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read out ciphertext */                                                                         \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config GCM in `TEXT` mode and write plaintext block 2 into the data registers */               \
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
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  write_request(AES_DATA_IN_0_OFFSET, 32'h53a9a786),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'hdaf73415),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h3d304c2e),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h728a318a),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read out ciphertext */                                                                         \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config GCM in `TEXT` mode and write plaintext block 3 into the data registers */               \
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
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  write_request(AES_DATA_IN_0_OFFSET, 32'h950c3c1c),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h53096895),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h240ecf2f),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h25b5a649),                                                \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_OUTPUT_VALID_OFFSET),                     \
                                                                                                    \
  /* Read out ciphertext  */                                                                        \
  read_request(AES_DATA_OUT_0_OFFSET),                                                              \
  read_request(AES_DATA_OUT_1_OFFSET),                                                              \
  read_request(AES_DATA_OUT_2_OFFSET),                                                              \
  read_request(AES_DATA_OUT_3_OFFSET),                                                              \
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  /* Config GCM in `TEXT` mode and write plaintext block 4 into the data registers */               \
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
  read_request(AES_STATUS_OFFSET, 32'(1'b1) << AES_STATUS_IDLE_OFFSET),                             \
                                                                                                    \
  write_request(AES_DATA_IN_0_OFFSET, 32'hf5ed6ab1),                                                \
  write_request(AES_DATA_IN_1_OFFSET, 32'h57e60daa),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h397b63ba),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h55d2af1a),                                                \
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
  write_request(AES_DATA_IN_1_OFFSET, 32'ha0000000),                                                \
  write_request(AES_DATA_IN_2_OFFSET, 32'h00000000),                                                \
  write_request(AES_DATA_IN_3_OFFSET, 32'h00020000),                                                \
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
