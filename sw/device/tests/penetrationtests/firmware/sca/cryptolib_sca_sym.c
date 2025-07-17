// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/cryptolib_sca_sym.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/firmware/sca/cryptolib_sca_sym_impl.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_sca_sym_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

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
  cryptolib_sca_aes_impl(data_in, data_in_len, key, key_len, iv, data_out,
                         data_out_len, padding, mode, op_enc, cfg_in, cfg_out,
                         trigger);
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
  TRY(cryptolib_sca_gcm_impl(data_in, data_in_len, aad, aad_len, key, key_len,
                             iv, data_out, data_out_len, tag, tag_len, cfg_in,
                             cfg_out, trigger));
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
  cryptolib_sca_hmac_impl(data_in, data_in_len, key, key_len, data_out,
                          data_out_len, padding, mode, cfg_in, cfg_out,
                          trigger);
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
  TRY(cryptolib_sca_drbg_impl(entropy, entropy_len, nonce, nonce_len, data_out,
                              data_out_len, reseed_interval, mode, cfg_in,
                              cfg_out, trigger));
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_aes_fvsr_plaintext(ujson_t *uj) {
  cryptolib_sca_sym_aes_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_aes_in_t(uj, &uj_input));

  uint8_t batch_data_in[uj_input.num_iterations][AES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[uj_input.num_iterations][AES_CMD_MAX_KEY_BYTES];

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
  cryptolib_sca_sym_aes_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_aes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_aes_fvsr_key(ujson_t *uj) {
  cryptolib_sca_sym_aes_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_aes_in_t(uj, &uj_input));

  uint8_t batch_data_in[uj_input.num_iterations][AES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[uj_input.num_iterations][AES_CMD_MAX_KEY_BYTES];

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
  cryptolib_sca_sym_aes_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_aes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_cmac_fvsr_plaintext(ujson_t *uj) {
  cryptolib_sca_sym_cmac_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_cmac_in_t(uj, &uj_input));

  uint8_t batch_data_in[uj_input.num_iterations][AES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[uj_input.num_iterations][AES_CMD_MAX_KEY_BYTES];

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
  cryptolib_sca_sym_cmac_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_cmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_cmac_fvsr_key(ujson_t *uj) {
  cryptolib_sca_sym_cmac_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_cmac_in_t(uj, &uj_input));

  uint8_t batch_data_in[uj_input.num_iterations][AES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[uj_input.num_iterations][AES_CMD_MAX_KEY_BYTES];

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
  cryptolib_sca_sym_cmac_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_cmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_gcm_fvsr_plaintext(ujson_t *uj) {
  cryptolib_sca_sym_gcm_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_gcm_in_t(uj, &uj_input));

  uint8_t batch_data_in[uj_input.num_iterations][AES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[uj_input.num_iterations][AES_CMD_MAX_KEY_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided key is used and the message is fixed. When
  // not sample_fixed, the provided key and a random message is
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
  size_t tag_len = 16;
  size_t cfg_out;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_gcm(batch_data_in[it], uj_input.data_len,
                              uj_input.aad, uj_input.aad_len, batch_keys[it],
                              uj_input.key_len, uj_input.iv, data_out_buf,
                              &data_out_len, tag_buf, &tag_len, uj_input.cfg,
                              &cfg_out, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_gcm_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  memcpy(uj_output.tag, tag_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.tag_len = tag_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_gcm_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_gcm_fvsr_key(ujson_t *uj) {
  cryptolib_sca_sym_gcm_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_gcm_in_t(uj, &uj_input));

  uint8_t batch_data_in[uj_input.num_iterations][AES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[uj_input.num_iterations][AES_CMD_MAX_KEY_BYTES];

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
  size_t tag_len = 16;
  size_t cfg_out;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_gcm(batch_data_in[it], uj_input.data_len,
                              uj_input.aad, uj_input.aad_len, batch_keys[it],
                              uj_input.key_len, uj_input.iv, data_out_buf,
                              &data_out_len, tag_buf, &tag_len, uj_input.cfg,
                              &cfg_out, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_gcm_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  memcpy(uj_output.tag, tag_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.tag_len = tag_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_gcm_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_tdes_fvsr_plaintext(ujson_t *uj) {
  cryptolib_sca_sym_tdes_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_tdes_in_t(uj, &uj_input));

  uint8_t batch_data_in[uj_input.num_iterations][TDES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[uj_input.num_iterations][TDES_CMD_MAX_KEY_BYTES];

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
  cryptolib_sca_sym_tdes_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, TDES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_tdes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_tdes_fvsr_key(ujson_t *uj) {
  cryptolib_sca_sym_tdes_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_tdes_in_t(uj, &uj_input));

  uint8_t batch_data_in[uj_input.num_iterations][TDES_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[uj_input.num_iterations][TDES_CMD_MAX_KEY_BYTES];

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
  cryptolib_sca_sym_tdes_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, TDES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_tdes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_hmac_fvsr_plaintext(ujson_t *uj) {
  cryptolib_sca_sym_hmac_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_hmac_in_t(uj, &uj_input));

  uint8_t batch_data_in[uj_input.num_iterations][HMAC_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[uj_input.num_iterations][HMAC_CMD_MAX_KEY_BYTES];

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
  cryptolib_sca_sym_hmac_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, HMAC_CMD_MAX_TAG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_hmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_hmac_fvsr_key(ujson_t *uj) {
  cryptolib_sca_sym_hmac_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_hmac_in_t(uj, &uj_input));

  uint8_t batch_data_in[uj_input.num_iterations][HMAC_CMD_MAX_MSG_BYTES];
  uint8_t batch_keys[uj_input.num_iterations][HMAC_CMD_MAX_KEY_BYTES];

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
  cryptolib_sca_sym_hmac_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, HMAC_CMD_MAX_TAG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_hmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_drbg_fvsr(ujson_t *uj) {
  cryptolib_sca_sym_drbg_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_drbg_in_t(uj, &uj_input));

  uint8_t batch_entropy[uj_input.num_iterations][DRBG_CMD_MAX_ENTROPY_BYTES];
  uint8_t batch_nonce[uj_input.num_iterations][DRBG_CMD_MAX_NONCE_BYTES];

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
  cryptolib_sca_sym_drbg_out_t uj_output;
  memcpy(uj_output.data, data_out_buf, DRBG_CMD_MAX_OUTPUT_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_drbg_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_init(ujson_t *uj) {
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
      &uj_output.sram_ret_readback_en, uj_cpuctrl_data.enable_data_ind_timing,
      &uj_output.data_ind_timing_en));

  // Read rom digest.
  TRY(pentest_read_rom_digest(uj_output.rom_digest));

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

status_t handle_cryptolib_sca_sym(ujson_t *uj) {
  cryptolib_sca_sym_subcommand_t cmd;
  TRY(ujson_deserialize_cryptolib_sca_sym_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kCryptoLibScaSymSubcommandAesFvsrPlaintext:
      return handle_cryptolib_sca_sym_aes_fvsr_plaintext(uj);
    case kCryptoLibScaSymSubcommandAesFvsrKey:
      return handle_cryptolib_sca_sym_aes_fvsr_key(uj);
    case kCryptoLibScaSymSubcommandCmacFvsrPlaintext:
      return handle_cryptolib_sca_sym_cmac_fvsr_plaintext(uj);
    case kCryptoLibScaSymSubcommandCmacFvsrKey:
      return handle_cryptolib_sca_sym_cmac_fvsr_key(uj);
    case kCryptoLibScaSymSubcommandGcmFvsrPlaintext:
      return handle_cryptolib_sca_sym_gcm_fvsr_plaintext(uj);
    case kCryptoLibScaSymSubcommandGcmFvsrKey:
      return handle_cryptolib_sca_sym_gcm_fvsr_key(uj);
    case kCryptoLibScaSymSubcommandTdesFvsrPlaintext:
      return handle_cryptolib_sca_sym_tdes_fvsr_plaintext(uj);
    case kCryptoLibScaSymSubcommandTdesFvsrKey:
      return handle_cryptolib_sca_sym_tdes_fvsr_key(uj);
    case kCryptoLibScaSymSubcommandHmacFvsrPlaintext:
      return handle_cryptolib_sca_sym_hmac_fvsr_plaintext(uj);
    case kCryptoLibScaSymSubcommandHmacFvsrKey:
      return handle_cryptolib_sca_sym_hmac_fvsr_key(uj);
    case kCryptoLibScaSymSubcommandDrbgFvsr:
      return handle_cryptolib_sca_sym_drbg_fvsr(uj);
    case kCryptoLibScaSymSubcommandInit:
      return handle_cryptolib_sca_sym_init(uj);
    default:
      LOG_ERROR("Unrecognized CryptoLib SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
