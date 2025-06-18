// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/cryptolib_sca.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_sca_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  /**
   * Max number of traces per batch.
   */
  kNumBatchOpsMax = 256,
};

static status_t trigger_cryptolib_aes(uint8_t data_in[AES_CMD_MAX_MSG_BYTES],
                                      size_t data_in_len,
                                      uint8_t key[AES_CMD_MAX_KEY_BYTES],
                                      size_t key_len,
                                      uint8_t iv[AES_CMD_MAX_BLOCK_BYTES],
                                      uint8_t data_out[AES_CMD_MAX_MSG_BYTES],
                                      size_t *data_out_len, size_t padding,
                                      size_t mode, bool op_enc, size_t cfg_in,
                                      size_t *cfg_out, size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform an AES encryption or decryption.
  // Adjust the mode of operation and the padding mode.
  // The total size of this test can be large due to all these options.
  // Triggers are over the API calls.

  memset(data_out, 0, AES_CMD_MAX_MSG_BYTES);
  *data_out_len = AES_CMD_MAX_MSG_BYTES;
  *cfg_out = 0;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

static status_t trigger_cryptolib_cmac(uint8_t data_in[AES_CMD_MAX_MSG_BYTES],
                                       size_t data_in_len,
                                       uint8_t key[AES_CMD_MAX_KEY_BYTES],
                                       size_t key_len,
                                       uint8_t iv[AES_CMD_MAX_BLOCK_BYTES],
                                       uint8_t data_out[AES_CMD_MAX_MSG_BYTES],
                                       size_t *data_out_len, size_t cfg_in,
                                       size_t *cfg_out, size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a CMAC encryption.
  // Verify the tag before sending the output.
  // Triggers are over the API calls.

  memset(data_out, 0, AES_CMD_MAX_MSG_BYTES);
  *data_out_len = AES_CMD_MAX_MSG_BYTES;
  *cfg_out = 0;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

static status_t trigger_cryptolib_gcm(
    uint8_t data_in[AES_CMD_MAX_MSG_BYTES], size_t data_in_len,
    uint8_t aad[AES_CMD_MAX_MSG_BYTES], size_t aad_len,
    uint8_t key[AES_CMD_MAX_KEY_BYTES], size_t key_len,
    uint8_t iv[AES_CMD_MAX_BLOCK_BYTES],
    uint8_t data_out[AES_CMD_MAX_MSG_BYTES], size_t *data_out_len,
    uint8_t tag[AES_CMD_MAX_MSG_BYTES], size_t *tag_len, size_t cfg_in,
    size_t *cfg_out, size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a GCM encryption with aad and generate a tag.
  // Then, verify that tag again, before sending the output.
  // Trigger are over the API calls.

  memset(data_out, 0, AES_CMD_MAX_MSG_BYTES);
  *data_out_len = AES_CMD_MAX_MSG_BYTES;
  memset(tag, 0, AES_CMD_MAX_MSG_BYTES);
  *tag_len = AES_CMD_MAX_MSG_BYTES;
  *cfg_out = 0;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

static status_t trigger_cryptolib_tdes(uint8_t data_in[TDES_CMD_MAX_MSG_BYTES],
                                       size_t data_in_len,
                                       uint8_t key[TDES_CMD_MAX_KEY_BYTES],
                                       size_t key_len,
                                       uint8_t iv[TDES_CMD_MAX_BLOCK_BYTES],
                                       uint8_t data_out[TDES_CMD_MAX_MSG_BYTES],
                                       size_t *data_out_len, size_t padding,
                                       size_t mode, bool op_enc, size_t cfg_in,
                                       size_t *cfg_out, size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a TDES encryption or decryption.
  // Adjust the mode of operation and the padding mode.
  // Triggers are over the API calls.

  memset(data_out, 0, TDES_CMD_MAX_MSG_BYTES);
  *data_out_len = TDES_CMD_MAX_MSG_BYTES;
  *cfg_out = 0;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

static status_t trigger_cryptolib_hmac(uint8_t data_in[HMAC_CMD_MAX_MSG_BYTES],
                                       size_t data_in_len,
                                       uint8_t key[HMAC_CMD_MAX_KEY_BYTES],
                                       size_t key_len,
                                       uint8_t data_out[HMAC_CMD_MAX_TAG_BYTES],
                                       size_t *data_out_len, size_t padding,
                                       size_t mode, size_t cfg_in,
                                       size_t *cfg_out, size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a TDES encryption or decryption.
  // Adjust the mode of operation and the padding mode.
  // Triggers are over the API calls.

  memset(data_out, 0, HMAC_CMD_MAX_TAG_BYTES);
  *data_out_len = HMAC_CMD_MAX_TAG_BYTES;
  *cfg_out = 0;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

static status_t trigger_cryptolib_drbg(
    uint8_t entropy[DRBG_CMD_MAX_ENTROPY_BYTES], size_t entropy_len,
    uint8_t nonce[DRBG_CMD_MAX_NONCE_BYTES], size_t nonce_len,
    uint8_t data_out[DRBG_CMD_MAX_OUTPUT_BYTES], size_t *data_out_len,
    size_t reseed_interval, size_t mode, size_t cfg_in, size_t *cfg_out,
    size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a TDES encryption or decryption.
  // Adjust the mode of operation and the padding mode.
  // Triggers are over the API calls.

  memset(data_out, 0, DRBG_CMD_MAX_OUTPUT_BYTES);
  *data_out_len = DRBG_CMD_MAX_OUTPUT_BYTES;
  *cfg_out = 0;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

status_t handle_cryptolib_sca_aes_fvsr_plaintext(ujson_t *uj) {
  cryptolib_sca_aes_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_aes_in_t(uj, &uj_input));

  uint8_t batch_data_in[kNumBatchOpsMax][AES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[kNumBatchOpsMax][AES_CMD_MAX_KEY_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided key is used and the message is random. When
  // not sample_fixed, a random key and a random message is
  // generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_data_in[it], uj_input.data, uj_input.data_len);
    } else {
      prng_rand_bytes(batch_data_in[it], uj_input.data_len);
    }
    memcpy(batch_keys[it], uj_input.key, uj_input.key_len);
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke AES for each data set.
  uint8_t data_out_buf[AES_CMD_MAX_MSG_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_aes(batch_data_in[it], uj_input.data_len,
                              batch_keys[it], uj_input.key_len, uj_input.iv,
                              data_out_buf, &data_out_len, uj_input.padding,
                              uj_input.mode, uj_input.op_enc, uj_input.cfg,
                              &cfg_out, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_aes_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_aes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_aes_fvsr_key(ujson_t *uj) {
  cryptolib_sca_aes_in_fvsr_key_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_aes_in_fvsr_key_t(uj, &uj_input));

  uint8_t batch_data_in[kNumBatchOpsMax][AES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[kNumBatchOpsMax][AES_CMD_MAX_KEY_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided key is used and the message is random. When
  // not sample_fixed, a random key and a random message is
  // generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_keys[it], uj_input.key, uj_input.key_len);
    } else {
      prng_rand_bytes(batch_keys[it], uj_input.key_len);
    }
    prng_rand_bytes(batch_data_in[it], uj_input.data_len);
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke AES for each data set.
  uint8_t data_out_buf[AES_CMD_MAX_MSG_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_aes(batch_data_in[it], uj_input.data_len,
                              batch_keys[it], uj_input.key_len, uj_input.iv,
                              data_out_buf, &data_out_len, uj_input.padding,
                              uj_input.mode, uj_input.op_enc, uj_input.cfg,
                              &cfg_out, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_aes_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_aes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_cmac_fvsr_plaintext(ujson_t *uj) {
  cryptolib_sca_cmac_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_cmac_in_t(uj, &uj_input));

  uint8_t batch_data_in[kNumBatchOpsMax][AES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[kNumBatchOpsMax][AES_CMD_MAX_KEY_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided key is used and the message is random. When
  // not sample_fixed, a random key and a random message is
  // generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_data_in[it], uj_input.data, uj_input.data_len);
    } else {
      prng_rand_bytes(batch_data_in[it], uj_input.data_len);
    }
    memcpy(batch_keys[it], uj_input.key, uj_input.key_len);
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke CMAC for each data set.
  uint8_t data_out_buf[AES_CMD_MAX_MSG_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_cmac(batch_data_in[it], uj_input.data_len,
                               batch_keys[it], uj_input.key_len, uj_input.iv,
                               data_out_buf, &data_out_len, uj_input.cfg,
                               &cfg_out, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_cmac_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_cmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_cmac_fvsr_key(ujson_t *uj) {
  cryptolib_sca_cmac_in_fvsr_key_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_cmac_in_fvsr_key_t(uj, &uj_input));

  uint8_t batch_data_in[kNumBatchOpsMax][AES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[kNumBatchOpsMax][AES_CMD_MAX_KEY_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided key is used and the message is random. When
  // not sample_fixed, a random key and a random message is
  // generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_keys[it], uj_input.key, uj_input.key_len);
    } else {
      prng_rand_bytes(batch_keys[it], uj_input.key_len);
    }
    prng_rand_bytes(batch_data_in[it], uj_input.data_len);
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke CMAC for each data set.
  uint8_t data_out_buf[AES_CMD_MAX_MSG_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_cmac(batch_data_in[it], uj_input.data_len,
                               batch_keys[it], uj_input.key_len, uj_input.iv,
                               data_out_buf, &data_out_len, uj_input.cfg,
                               &cfg_out, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_cmac_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_cmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_gcm_fvsr_plaintext(ujson_t *uj) {
  cryptolib_sca_gcm_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_gcm_in_t(uj, &uj_input));

  uint8_t batch_data_in[kNumBatchOpsMax][AES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[kNumBatchOpsMax][AES_CMD_MAX_KEY_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided key is used and the message is random. When
  // not sample_fixed, a random key and a random message is
  // generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_data_in[it], uj_input.data, uj_input.data_len);
    } else {
      prng_rand_bytes(batch_data_in[it], uj_input.data_len);
    }
    memcpy(batch_keys[it], uj_input.key, uj_input.key_len);
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke GCM for each data set.
  uint8_t data_out_buf[AES_CMD_MAX_MSG_BYTES];
  size_t data_out_len;
  uint8_t tag_buf[AES_CMD_MAX_MSG_BYTES];
  size_t tag_len;
  size_t cfg_out;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_gcm(batch_data_in[it], uj_input.data_len,
                              uj_input.aad, uj_input.aad_len, batch_keys[it],
                              uj_input.key_len, uj_input.iv, data_out_buf,
                              &data_out_len, tag_buf, &tag_len, uj_input.cfg,
                              &cfg_out, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_gcm_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  memcpy(uj_output.tag, tag_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.tag_len = tag_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_gcm_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_gcm_fvsr_key(ujson_t *uj) {
  cryptolib_sca_gcm_in_fvsr_key_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_gcm_in_fvsr_key_t(uj, &uj_input));

  uint8_t batch_data_in[kNumBatchOpsMax][AES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[kNumBatchOpsMax][AES_CMD_MAX_KEY_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided key is used and the message is random. When
  // not sample_fixed, a random key and a random message is
  // generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_keys[it], uj_input.key, uj_input.key_len);
    } else {
      prng_rand_bytes(batch_keys[it], uj_input.key_len);
    }
    prng_rand_bytes(batch_data_in[it], uj_input.data_len);
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke GCM for each data set.
  uint8_t data_out_buf[AES_CMD_MAX_MSG_BYTES];
  size_t data_out_len;
  uint8_t tag_buf[AES_CMD_MAX_MSG_BYTES];
  size_t tag_len;
  size_t cfg_out;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_gcm(batch_data_in[it], uj_input.data_len,
                              uj_input.aad, uj_input.aad_len, batch_keys[it],
                              uj_input.key_len, uj_input.iv, data_out_buf,
                              &data_out_len, tag_buf, &tag_len, uj_input.cfg,
                              &cfg_out, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_gcm_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  memcpy(uj_output.tag, tag_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.tag_len = tag_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_gcm_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_tdes_fvsr_plaintext(ujson_t *uj) {
  cryptolib_sca_tdes_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_tdes_in_t(uj, &uj_input));

  uint8_t batch_data_in[kNumBatchOpsMax][TDES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[kNumBatchOpsMax][TDES_CMD_MAX_KEY_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided key is used and the message is random. When
  // not sample_fixed, a random key and a random message is
  // generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_data_in[it], uj_input.data, uj_input.data_len);
    } else {
      prng_rand_bytes(batch_data_in[it], uj_input.data_len);
    }
    memcpy(batch_keys[it], uj_input.key, uj_input.key_len);
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke TDES for each data set.
  uint8_t data_out_buf[TDES_CMD_MAX_MSG_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_tdes(batch_data_in[it], uj_input.data_len,
                               batch_keys[it], uj_input.key_len, uj_input.iv,
                               data_out_buf, &data_out_len, uj_input.padding,
                               uj_input.mode, uj_input.op_enc, uj_input.cfg,
                               &cfg_out, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_tdes_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, TDES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_tdes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_tdes_fvsr_key(ujson_t *uj) {
  cryptolib_sca_tdes_in_fvsr_key_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_tdes_in_fvsr_key_t(uj, &uj_input));

  uint8_t batch_data_in[kNumBatchOpsMax][TDES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[kNumBatchOpsMax][TDES_CMD_MAX_KEY_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided key is used and the message is random. When
  // not sample_fixed, a random key and a random message is
  // generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_keys[it], uj_input.key, uj_input.key_len);
    } else {
      prng_rand_bytes(batch_keys[it], uj_input.key_len);
    }
    prng_rand_bytes(batch_data_in[it], uj_input.data_len);
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke TDES for each data set.
  uint8_t data_out_buf[TDES_CMD_MAX_MSG_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_tdes(batch_data_in[it], uj_input.data_len,
                               batch_keys[it], uj_input.key_len, uj_input.iv,
                               data_out_buf, &data_out_len, uj_input.padding,
                               uj_input.mode, uj_input.op_enc, uj_input.cfg,
                               &cfg_out, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_tdes_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, TDES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_tdes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_hmac_fvsr_plaintext(ujson_t *uj) {
  cryptolib_sca_hmac_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_hmac_in_t(uj, &uj_input));

  uint8_t batch_data_in[kNumBatchOpsMax][HMAC_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[kNumBatchOpsMax][HMAC_CMD_MAX_KEY_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided key is used and the message is random. When
  // not sample_fixed, a random key and a random message is
  // generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_data_in[it], uj_input.data, uj_input.data_len);
    } else {
      prng_rand_bytes(batch_data_in[it], uj_input.data_len);
    }
    memcpy(batch_keys[it], uj_input.key, uj_input.key_len);
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke HMAC for each data set.
  uint8_t data_out_buf[HMAC_CMD_MAX_TAG_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_hmac(batch_data_in[it], uj_input.data_len,
                               batch_keys[it], uj_input.key_len, data_out_buf,
                               &data_out_len, uj_input.padding, uj_input.mode,
                               uj_input.cfg, &cfg_out, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_hmac_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, HMAC_CMD_MAX_TAG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_hmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_hmac_fvsr_key(ujson_t *uj) {
  cryptolib_sca_hmac_in_fvsr_key_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_hmac_in_fvsr_key_t(uj, &uj_input));

  uint8_t batch_data_in[kNumBatchOpsMax][HMAC_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[kNumBatchOpsMax][HMAC_CMD_MAX_KEY_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided key is used and the message is random. When
  // not sample_fixed, a random key and a random message is
  // generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_keys[it], uj_input.key, uj_input.key_len);
    } else {
      prng_rand_bytes(batch_keys[it], uj_input.key_len);
    }
    prng_rand_bytes(batch_data_in[it], uj_input.data_len);
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke HMAC for each data set.
  uint8_t data_out_buf[HMAC_CMD_MAX_TAG_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_hmac(batch_data_in[it], uj_input.data_len,
                               batch_keys[it], uj_input.key_len, data_out_buf,
                               &data_out_len, uj_input.padding, uj_input.mode,
                               uj_input.cfg, &cfg_out, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_hmac_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, HMAC_CMD_MAX_TAG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_hmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_drbg_fvsr(ujson_t *uj) {
  cryptolib_sca_drbg_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_drbg_in_t(uj, &uj_input));

  uint8_t batch_entropy[kNumBatchOpsMax][DRBG_CMD_MAX_ENTROPY_BYTES];
  uint8_t batch_nonce[kNumBatchOpsMax][DRBG_CMD_MAX_NONCE_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided entropy is used and the nonce is random. When
  // not sample_fixed, a random entropy and a random nonce is
  // generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_entropy[it], uj_input.entropy, uj_input.entropy_len);
    } else {
      prng_rand_bytes(batch_entropy[it], uj_input.entropy_len);
    }
    prng_rand_bytes(batch_nonce[it], uj_input.nonce_len);
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke DRBG for each data set.
  uint8_t data_out_buf[DRBG_CMD_MAX_OUTPUT_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_drbg(batch_entropy[it], uj_input.entropy_len,
                               batch_nonce[it], uj_input.nonce_len,
                               data_out_buf, &data_out_len,
                               uj_input.reseed_interval, uj_input.mode,
                               uj_input.cfg, &cfg_out, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_drbg_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, DRBG_CMD_MAX_OUTPUT_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_drbg_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_rsa_dec(ujson_t *uj) {
  cryptolib_sca_rsa_dec_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_rsa_dec_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform an RSA decryption.
  // Adjust the hashing and the padding mode.
  // Triggers are over the API calls.

  cryptolib_sca_rsa_dec_out_t uj_output;
  memset(uj_output.n, 0, RSA_CMD_MAX_N_BYTES);
  memset(uj_output.d, 0, RSA_CMD_MAX_N_BYTES);
  uj_output.n_len = RSA_CMD_MAX_N_BYTES;
  memset(uj_output.data, 0, RSA_CMD_MAX_MESSAGE_BYTES);
  uj_output.data_len = RSA_CMD_MAX_MESSAGE_BYTES;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_rsa_dec_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_rsa_sign(ujson_t *uj) {
  cryptolib_sca_rsa_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_rsa_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform an RSA sign.
  // Adjust the hashing and the padding mode.
  // Triggers are over the API calls.

  cryptolib_sca_rsa_sign_out_t uj_output;
  memset(uj_output.n, 0, RSA_CMD_MAX_N_BYTES);
  memset(uj_output.d, 0, RSA_CMD_MAX_N_BYTES);
  uj_output.n_len = RSA_CMD_MAX_N_BYTES;
  memset(uj_output.sig, 0, RSA_CMD_MAX_SIGNATURE_BYTES);
  uj_output.sig_len = RSA_CMD_MAX_SIGNATURE_BYTES;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_rsa_sign_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_prime(ujson_t *uj) {
  cryptolib_sca_prime_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_prime_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Generates a prime.
  // Triggers are over the API calls.

  cryptolib_sca_prime_out_t uj_output;
  memset(uj_output.prime, 0, RSA_CMD_MAX_N_BYTES);
  uj_output.prime_len = RSA_CMD_MAX_N_BYTES;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_prime_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_p256_base_mul(ujson_t *uj) {
  cryptolib_sca_p256_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_p256_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in P256.
  // Trigger are over the API calls.

  cryptolib_sca_p256_base_mul_out_t uj_output;
  memset(uj_output.x, 0, P256_CMD_BYTES);
  memset(uj_output.y, 0, P256_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_p256_base_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_p256_point_mul(ujson_t *uj) {
  cryptolib_sca_p256_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_p256_point_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in P256.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  cryptolib_sca_p256_point_mul_out_t uj_output;
  memset(uj_output.x, 0, P256_CMD_BYTES);
  memset(uj_output.y, 0, P256_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_p256_point_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_p256_sign(ujson_t *uj) {
  cryptolib_sca_p256_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_p256_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a P256 signature.
  // Trigger are over the API calls.

  cryptolib_sca_p256_sign_out_t uj_output;
  memset(uj_output.pubx, 0, P256_CMD_BYTES);
  memset(uj_output.puby, 0, P256_CMD_BYTES);
  memset(uj_output.r, 0, P256_CMD_BYTES);
  memset(uj_output.s, 0, P256_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_p256_sign_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_p384_base_mul(ujson_t *uj) {
  cryptolib_sca_p384_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_p384_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in p384.
  // Trigger are over the API calls.

  cryptolib_sca_p384_base_mul_out_t uj_output;
  memset(uj_output.x, 0, P384_CMD_BYTES);
  memset(uj_output.y, 0, P384_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_p384_base_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_p384_point_mul(ujson_t *uj) {
  cryptolib_sca_p384_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_p384_point_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in p384.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  cryptolib_sca_p384_point_mul_out_t uj_output;
  memset(uj_output.x, 0, P384_CMD_BYTES);
  memset(uj_output.y, 0, P384_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_p384_point_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_p384_sign(ujson_t *uj) {
  cryptolib_sca_p384_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_p384_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a p384 signature.
  // Trigger are over the API calls.

  cryptolib_sca_p384_sign_out_t uj_output;
  memset(uj_output.pubx, 0, P384_CMD_BYTES);
  memset(uj_output.puby, 0, P384_CMD_BYTES);
  memset(uj_output.r, 0, P384_CMD_BYTES);
  memset(uj_output.s, 0, P384_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_p384_sign_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_secp256k1_base_mul(ujson_t *uj) {
  cryptolib_sca_secp256k1_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_secp256k1_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in secp256k1.
  // Trigger are over the API calls.

  cryptolib_sca_secp256k1_base_mul_out_t uj_output;
  memset(uj_output.x, 0, SECP256K1_CMD_BYTES);
  memset(uj_output.y, 0, SECP256K1_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_secp256k1_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_secp256k1_point_mul(ujson_t *uj) {
  cryptolib_sca_secp256k1_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_secp256k1_point_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in secp256k1.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  cryptolib_sca_secp256k1_point_mul_out_t uj_output;
  memset(uj_output.x, 0, SECP256K1_CMD_BYTES);
  memset(uj_output.y, 0, SECP256K1_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_secp256k1_point_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_secp256k1_sign(ujson_t *uj) {
  cryptolib_sca_secp256k1_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_secp256k1_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a secp256k1 signature.
  // Trigger are over the API calls.

  cryptolib_sca_secp256k1_sign_out_t uj_output;
  memset(uj_output.pubx, 0, SECP256K1_CMD_BYTES);
  memset(uj_output.puby, 0, SECP256K1_CMD_BYTES);
  memset(uj_output.r, 0, SECP256K1_CMD_BYTES);
  memset(uj_output.s, 0, SECP256K1_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_secp256k1_sign_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_x25519_base_mul(ujson_t *uj) {
  cryptolib_sca_x25519_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_x25519_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in X25519.
  // Trigger are over the API calls.

  cryptolib_sca_x25519_base_mul_out_t uj_output;
  memset(uj_output.x, 0, X25519_CMD_BYTES);
  memset(uj_output.y, 0, X25519_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_x25519_base_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_x25519_point_mul(ujson_t *uj) {
  cryptolib_sca_x25519_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_x25519_point_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in X25519.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  cryptolib_sca_x25519_point_mul_out_t uj_output;
  memset(uj_output.x, 0, X25519_CMD_BYTES);
  memset(uj_output.y, 0, X25519_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_x25519_point_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_ed25519_base_mul(ujson_t *uj) {
  cryptolib_sca_ed25519_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_ed25519_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in ED25519.
  // Trigger are over the API calls.

  cryptolib_sca_ed25519_base_mul_out_t uj_output;
  memset(uj_output.x, 0, ED25519_CMD_SCALAR_BYTES);
  memset(uj_output.y, 0, ED25519_CMD_SCALAR_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_ed25519_base_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_ed25519_sign(ujson_t *uj) {
  cryptolib_sca_ed25519_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_ed25519_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a ED25519 signature.
  // Trigger are over the API calls.

  cryptolib_sca_ed25519_sign_out_t uj_output;
  memset(uj_output.pubx, 0, ED25519_CMD_SCALAR_BYTES);
  memset(uj_output.puby, 0, ED25519_CMD_SCALAR_BYTES);
  memset(uj_output.r, 0, ED25519_CMD_SIG_BYTES);
  memset(uj_output.s, 0, ED25519_CMD_SIG_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_ed25519_sign_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_init(ujson_t *uj) {
  penetrationtest_cpuctrl_t uj_cpuctrl_data;
  TRY(ujson_deserialize_penetrationtest_cpuctrl_t(uj, &uj_cpuctrl_data));
  penetrationtest_sensor_config_t uj_sensor_data;
  TRY(ujson_deserialize_penetrationtest_sensor_config_t(uj, &uj_sensor_data));
  penetrationtest_alert_config_t uj_alert_data;
  TRY(ujson_deserialize_penetrationtest_alert_config_t(uj, &uj_alert_data));

  pentest_select_trigger_type(kPentestTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // pentest_init is not needed. kPentestTriggerSourceAes is selected as a
  // placeholder.
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralEdn |
                   kPentestPeripheralCsrng | kPentestPeripheralEntropy |
                   kPentestPeripheralAes | kPentestPeripheralHmac |
                   kPentestPeripheralKmac | kPentestPeripheralOtbn,
               uj_sensor_data.sensor_ctrl_enable,
               uj_sensor_data.sensor_ctrl_en_fatal);

  // Configure the alert handler. Alerts triggered by IP blocks are captured
  // and reported to the test.
  pentest_configure_alert_handler(
      uj_alert_data.alert_classes, uj_alert_data.enable_alerts,
      uj_alert_data.enable_classes, uj_alert_data.accumulation_thresholds,
      uj_alert_data.signals, uj_alert_data.duration_cycles,
      uj_alert_data.ping_timeout);

  // Configure the CPU for the pentest.
  penetrationtest_device_info_t uj_output;
  TRY(pentest_configure_cpu(
      uj_cpuctrl_data.enable_icache, &uj_output.icache_en,
      uj_cpuctrl_data.enable_dummy_instr, &uj_output.dummy_instr_en,
      uj_cpuctrl_data.dummy_instr_count, uj_cpuctrl_data.enable_jittery_clock,
      uj_cpuctrl_data.enable_sram_readback, &uj_output.clock_jitter_locked,
      &uj_output.clock_jitter_en, &uj_output.sram_main_readback_locked,
      &uj_output.sram_ret_readback_locked, &uj_output.sram_main_readback_en,
      &uj_output.sram_ret_readback_en));

  // Read device ID and return to host.
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_info_t, uj, &uj_output);

  // Read the sensor config.
  TRY(pentest_send_sensor_config(uj));

  // Read the alert config.
  TRY(pentest_send_alert_config(uj));

  // Read different SKU config fields and return to host.
  TRY(pentest_send_sku_config(uj));

  /////////////// STUB START ///////////////
  // Add things like versioning.
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

status_t handle_cryptolib_sca(ujson_t *uj) {
  cryptolib_sca_subcommand_t cmd;
  TRY(ujson_deserialize_cryptolib_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kCryptoLibScaSubcommandAesFvsrPlaintext:
      return handle_cryptolib_sca_aes_fvsr_plaintext(uj);
    case kCryptoLibScaSubcommandAesFvsrKey:
      return handle_cryptolib_sca_aes_fvsr_key(uj);
    case kCryptoLibScaSubcommandCmacFvsrPlaintext:
      return handle_cryptolib_sca_cmac_fvsr_plaintext(uj);
    case kCryptoLibScaSubcommandCmacFvsrKey:
      return handle_cryptolib_sca_cmac_fvsr_key(uj);
    case kCryptoLibScaSubcommandGcmFvsrPlaintext:
      return handle_cryptolib_sca_gcm_fvsr_plaintext(uj);
    case kCryptoLibScaSubcommandGcmFvsrKey:
      return handle_cryptolib_sca_gcm_fvsr_key(uj);
    case kCryptoLibScaSubcommandTdesFvsrPlaintext:
      return handle_cryptolib_sca_tdes_fvsr_plaintext(uj);
    case kCryptoLibScaSubcommandTdesFvsrKey:
      return handle_cryptolib_sca_tdes_fvsr_key(uj);
    case kCryptoLibScaSubcommandHmacFvsrPlaintext:
      return handle_cryptolib_sca_hmac_fvsr_plaintext(uj);
    case kCryptoLibScaSubcommandHmacFvsrKey:
      return handle_cryptolib_sca_hmac_fvsr_key(uj);
    case kCryptoLibScaSubcommandDrbgFvsr:
      return handle_cryptolib_sca_drbg_fvsr(uj);
    case kCryptoLibScaSubcommandRsaDec:
      return handle_cryptolib_sca_rsa_dec(uj);
    case kCryptoLibScaSubcommandRsaSign:
      return handle_cryptolib_sca_rsa_sign(uj);
    case kCryptoLibScaSubcommandPrime:
      return handle_cryptolib_sca_prime(uj);
    case kCryptoLibScaSubcommandP256BaseMul:
      return handle_cryptolib_sca_p256_base_mul(uj);
    case kCryptoLibScaSubcommandP256PointMul:
      return handle_cryptolib_sca_p256_point_mul(uj);
    case kCryptoLibScaSubcommandP256Sign:
      return handle_cryptolib_sca_p256_sign(uj);
    case kCryptoLibScaSubcommandP384BaseMul:
      return handle_cryptolib_sca_p384_base_mul(uj);
    case kCryptoLibScaSubcommandP384PointMul:
      return handle_cryptolib_sca_p384_point_mul(uj);
    case kCryptoLibScaSubcommandP384Sign:
      return handle_cryptolib_sca_p384_sign(uj);
    case kCryptoLibScaSubcommandSecp256k1BaseMul:
      return handle_cryptolib_sca_secp256k1_base_mul(uj);
    case kCryptoLibScaSubcommandSecp256k1PointMul:
      return handle_cryptolib_sca_secp256k1_point_mul(uj);
    case kCryptoLibScaSubcommandSecp256k1Sign:
      return handle_cryptolib_sca_secp256k1_sign(uj);
    case kCryptoLibScaSubcommandX25519BaseMul:
      return handle_cryptolib_sca_x25519_base_mul(uj);
    case kCryptoLibScaSubcommandX25519PointMul:
      return handle_cryptolib_sca_x25519_point_mul(uj);
    case kCryptoLibScaSubcommandEd25519BaseMul:
      return handle_cryptolib_sca_ed25519_base_mul(uj);
    case kCryptoLibScaSubcommandEd25519Sign:
      return handle_cryptolib_sca_ed25519_sign(uj);
    case kCryptoLibScaSubcommandInit:
      return handle_cryptolib_sca_init(uj);
    default:
      LOG_ERROR("Unrecognized CryptoLib SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
