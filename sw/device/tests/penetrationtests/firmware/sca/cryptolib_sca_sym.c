// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/cryptolib_sca_sym.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/security_config.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/firmware/sca/cryptolib_sca_sym_impl.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_sca_sym_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static status_t trigger_cryptolib_aes(
    uint8_t data_in[AES_CMD_MAX_MSG_BYTES], size_t data_in_len,
    uint8_t key[AES_CMD_MAX_KEY_BYTES], size_t key_len,
    uint8_t iv[AES_CMD_MAX_BLOCK_BYTES],
    uint8_t data_out[AES_CMD_MAX_MSG_BYTES], size_t *data_out_len,
    size_t padding, size_t mode, bool op_enc, size_t cfg_in, size_t *cfg_out,
    size_t *status, size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform an AES encryption or decryption.
  // Adjust the mode of operation and the padding mode.
  // The total size of this test can be large due to all these options.
  // Triggers are over the API calls.
  memset(data_out, 0, AES_CMD_MAX_MSG_BYTES);
  *data_out_len = AES_CMD_MAX_MSG_BYTES;
  *cfg_out = 0;
  *status = (size_t)cryptolib_sca_aes_impl(
                data_in, data_in_len, key, key_len, iv, data_out, data_out_len,
                padding, mode, op_enc, cfg_in, cfg_out, trigger)
                .value;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

static status_t trigger_cryptolib_cmac(
    uint8_t data_in[AES_CMD_MAX_MSG_BYTES], size_t data_in_len,
    uint8_t key[AES_CMD_MAX_KEY_BYTES], size_t key_len,
    uint8_t iv[AES_CMD_MAX_BLOCK_BYTES],
    uint8_t data_out[AES_CMD_MAX_MSG_BYTES], size_t *data_out_len,
    size_t cfg_in, size_t *cfg_out, size_t *status, size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a CMAC encryption.
  // Verify the tag before sending the output.
  // Triggers are over the API calls.

  memset(data_out, 0, AES_CMD_MAX_MSG_BYTES);
  *data_out_len = AES_CMD_MAX_MSG_BYTES;
  *cfg_out = 0;
  *status = 0;
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
    size_t *cfg_out, size_t *status, size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a GCM encryption with aad and generate a tag.
  // Then, verify that tag again, before sending the output.
  // Trigger are over the API calls.
  *status = (size_t)cryptolib_sca_gcm_impl(
                data_in, data_in_len, aad, aad_len, key, key_len, iv, data_out,
                data_out_len, tag, tag_len, cfg_in, cfg_out, trigger)
                .value;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

static status_t trigger_cryptolib_tdes(
    uint8_t data_in[TDES_CMD_MAX_MSG_BYTES], size_t data_in_len,
    uint8_t key[TDES_CMD_MAX_KEY_BYTES], size_t key_len,
    uint8_t iv[TDES_CMD_MAX_BLOCK_BYTES],
    uint8_t data_out[TDES_CMD_MAX_MSG_BYTES], size_t *data_out_len,
    size_t padding, size_t mode, bool op_enc, size_t cfg_in, size_t *cfg_out,
    size_t *status, size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a TDES encryption or decryption.
  // Adjust the mode of operation and the padding mode.
  // Triggers are over the API calls.

  memset(data_out, 0, TDES_CMD_MAX_MSG_BYTES);
  *data_out_len = TDES_CMD_MAX_MSG_BYTES;
  *cfg_out = 0;
  *status = 0;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

static status_t trigger_cryptolib_hmac(
    uint8_t data_in[HMAC_CMD_MAX_MSG_BYTES], size_t data_in_len,
    uint8_t key[HMAC_CMD_MAX_KEY_BYTES], size_t key_len,
    uint8_t data_out[HMAC_CMD_MAX_TAG_BYTES], size_t *data_out_len,
    size_t padding, size_t mode, size_t cfg_in, size_t *cfg_out, size_t *status,
    size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a TDES encryption or decryption.
  // Adjust the mode of operation and the padding mode.
  // Triggers are over the API calls.
  *status = (size_t)cryptolib_sca_hmac_impl(data_in, data_in_len, key, key_len,
                                            data_out, data_out_len, padding,
                                            mode, cfg_in, cfg_out, trigger)
                .value;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

static status_t trigger_cryptolib_drbg_generate(
    uint8_t nonce[DRBG_CMD_MAX_NONCE_BYTES], size_t nonce_len,
    uint8_t data_out[DRBG_CMD_MAX_OUTPUT_BYTES], size_t data_out_len,
    size_t mode, size_t cfg_in, size_t *cfg_out, size_t *status,
    size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a TDES encryption or decryption.
  // Adjust the mode of operation and the padding mode.
  // Triggers are over the API calls.
  *status = (size_t)cryptolib_sca_drbg_generate_impl(nonce, nonce_len, data_out,
                                                     data_out_len, mode, cfg_in,
                                                     cfg_out, trigger)
                .value;
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
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_aes(batch_data_in[it], uj_input.data_len,
                              batch_keys[it], uj_input.key_len, uj_input.iv,
                              data_out_buf, &data_out_len, uj_input.padding,
                              uj_input.mode, uj_input.op_enc, uj_input.cfg,
                              &cfg_out, &status, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_aes_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
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
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_aes(batch_data_in[it], uj_input.data_len,
                              batch_keys[it], uj_input.key_len, uj_input.iv,
                              data_out_buf, &data_out_len, uj_input.padding,
                              uj_input.mode, uj_input.op_enc, uj_input.cfg,
                              &cfg_out, &status, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_aes_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_aes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_aes_daisy_chain(ujson_t *uj) {
  cryptolib_sca_sym_aes_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_aes_in_t(uj, &uj_input));

  // Fix the key
  uint8_t key[AES_CMD_MAX_KEY_BYTES];
  // Pad with zero
  memset(key, 0, AES_CMD_MAX_KEY_BYTES);
  memcpy(key, uj_input.key, uj_input.key_len);

  // Invoke AES for each data set.
  uint8_t data_in_buf[AES_CMD_MAX_MSG_BYTES];
  uint8_t data_out_buf[AES_CMD_MAX_MSG_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  size_t status;
  // Pad with zeros
  memset(data_in_buf, 0, AES_CMD_MAX_MSG_BYTES);
  memcpy(data_in_buf, uj_input.data, uj_input.data_len);
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_aes(
        data_in_buf, uj_input.data_len, key, uj_input.key_len, uj_input.iv,
        data_out_buf, &data_out_len, uj_input.padding, uj_input.mode,
        uj_input.op_enc, uj_input.cfg, &cfg_out, &status, uj_input.trigger));
    // Copy output to input
    memset(data_in_buf, 0, uj_input.data_len);
    memcpy(data_in_buf, data_out_buf, uj_input.data_len);
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_aes_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
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
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_cmac(batch_data_in[it], uj_input.data_len,
                               batch_keys[it], uj_input.key_len, uj_input.iv,
                               data_out_buf, &data_out_len, uj_input.cfg,
                               &cfg_out, &status, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_cmac_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
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
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_cmac(batch_data_in[it], uj_input.data_len,
                               batch_keys[it], uj_input.key_len, uj_input.iv,
                               data_out_buf, &data_out_len, uj_input.cfg,
                               &cfg_out, &status, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_cmac_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_cmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_cmac_daisy_chain(ujson_t *uj) {
  cryptolib_sca_sym_cmac_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_cmac_in_t(uj, &uj_input));

  // Fix the key
  uint8_t key[AES_CMD_MAX_KEY_BYTES];
  // Pad with zero
  memset(key, 0, AES_CMD_MAX_KEY_BYTES);
  memcpy(key, uj_input.key, uj_input.key_len);

  // Invoke CMAC for each data set.
  uint8_t data_in_buf[AES_CMD_MAX_MSG_BYTES];
  uint8_t data_out_buf[AES_CMD_MAX_MSG_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  size_t status;
  // Pad with zeros
  memset(data_in_buf, 0, AES_CMD_MAX_MSG_BYTES);
  memcpy(data_in_buf, uj_input.data, uj_input.data_len);
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_cmac(data_in_buf, uj_input.data_len, key,
                               uj_input.key_len, uj_input.iv, data_out_buf,
                               &data_out_len, uj_input.cfg, &cfg_out, &status,
                               uj_input.trigger));
    // Copy output to input
    memset(data_in_buf, 0, uj_input.data_len);
    memcpy(data_in_buf, data_out_buf, uj_input.data_len);
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_cmac_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
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
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_gcm(batch_data_in[it], uj_input.data_len,
                              uj_input.aad, uj_input.aad_len, batch_keys[it],
                              uj_input.key_len, uj_input.iv, data_out_buf,
                              &data_out_len, tag_buf, &tag_len, uj_input.cfg,
                              &cfg_out, &status, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_gcm_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  memcpy(uj_output.tag, tag_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.tag_len = tag_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
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
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_gcm(batch_data_in[it], uj_input.data_len,
                              uj_input.aad, uj_input.aad_len, batch_keys[it],
                              uj_input.key_len, uj_input.iv, data_out_buf,
                              &data_out_len, tag_buf, &tag_len, uj_input.cfg,
                              &cfg_out, &status, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_gcm_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  memcpy(uj_output.tag, tag_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.tag_len = tag_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_gcm_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_gcm_daisy_chain(ujson_t *uj) {
  cryptolib_sca_sym_gcm_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_gcm_in_t(uj, &uj_input));

  // Fix the key
  uint8_t key[AES_CMD_MAX_KEY_BYTES];
  // Pad with zero
  memset(key, 0, AES_CMD_MAX_KEY_BYTES);
  memcpy(key, uj_input.key, uj_input.key_len);

  // Invoke GCM for each data set.
  uint8_t data_in_buf[AES_CMD_MAX_MSG_BYTES];
  uint8_t data_out_buf[AES_CMD_MAX_MSG_BYTES];
  size_t data_out_len;
  uint8_t tag_buf[AES_CMD_MAX_MSG_BYTES];
  size_t tag_len = 16;
  size_t cfg_out;
  size_t status;
  // Pad with zeros
  memset(data_in_buf, 0, AES_CMD_MAX_MSG_BYTES);
  memcpy(data_in_buf, uj_input.data, uj_input.data_len);
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_gcm(
        data_in_buf, uj_input.data_len, uj_input.aad, uj_input.aad_len, key,
        uj_input.key_len, uj_input.iv, data_out_buf, &data_out_len, tag_buf,
        &tag_len, uj_input.cfg, &cfg_out, &status, uj_input.trigger));
    // Copy output to input
    memset(data_in_buf, 0, uj_input.data_len);
    memcpy(data_in_buf, data_out_buf, uj_input.data_len);
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_gcm_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  memcpy(uj_output.tag, tag_buf, AES_CMD_MAX_MSG_BYTES);
  uj_output.tag_len = tag_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
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
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_tdes(batch_data_in[it], uj_input.data_len,
                               batch_keys[it], uj_input.key_len, uj_input.iv,
                               data_out_buf, &data_out_len, uj_input.padding,
                               uj_input.mode, uj_input.op_enc, uj_input.cfg,
                               &cfg_out, &status, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_tdes_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, TDES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
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
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_tdes(batch_data_in[it], uj_input.data_len,
                               batch_keys[it], uj_input.key_len, uj_input.iv,
                               data_out_buf, &data_out_len, uj_input.padding,
                               uj_input.mode, uj_input.op_enc, uj_input.cfg,
                               &cfg_out, &status, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_tdes_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, TDES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_tdes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_tdes_daisy_chain(ujson_t *uj) {
  cryptolib_sca_sym_tdes_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_tdes_in_t(uj, &uj_input));

  // Fix the key
  uint8_t key[TDES_CMD_MAX_KEY_BYTES];
  // Pad with zero
  memset(key, 0, TDES_CMD_MAX_KEY_BYTES);
  memcpy(key, uj_input.key, uj_input.key_len);

  // Invoke TDES for each data set.
  uint8_t data_in_buf[TDES_CMD_MAX_MSG_BYTES];
  uint8_t data_out_buf[TDES_CMD_MAX_MSG_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  size_t status;
  // Pad with zeros
  memset(data_in_buf, 0, TDES_CMD_MAX_MSG_BYTES);
  memcpy(data_in_buf, uj_input.data, uj_input.data_len);
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_tdes(
        data_in_buf, uj_input.data_len, key, uj_input.key_len, uj_input.iv,
        data_out_buf, &data_out_len, uj_input.padding, uj_input.mode,
        uj_input.op_enc, uj_input.cfg, &cfg_out, &status, uj_input.trigger));
    // Copy output to input
    memset(data_in_buf, 0, uj_input.data_len);
    memcpy(data_in_buf, data_out_buf, uj_input.data_len);
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_tdes_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, TDES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
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
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_hmac(
        batch_data_in[it], uj_input.data_len, batch_keys[it], uj_input.key_len,
        data_out_buf, &data_out_len, uj_input.padding, uj_input.mode,
        uj_input.cfg, &cfg_out, &status, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_hmac_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, HMAC_CMD_MAX_TAG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
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
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_hmac(
        batch_data_in[it], uj_input.data_len, batch_keys[it], uj_input.key_len,
        data_out_buf, &data_out_len, uj_input.padding, uj_input.mode,
        uj_input.cfg, &cfg_out, &status, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_hmac_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, HMAC_CMD_MAX_TAG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_hmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_hmac_daisy_chain(ujson_t *uj) {
  cryptolib_sca_sym_hmac_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_hmac_in_t(uj, &uj_input));

  // Fix the key
  uint8_t key[HMAC_CMD_MAX_KEY_BYTES];
  // Pad with zero
  memset(key, 0, HMAC_CMD_MAX_KEY_BYTES);
  memcpy(key, uj_input.key, uj_input.key_len);

  // Invoke HMAC for each data set.
  uint8_t data_in_buf[HMAC_CMD_MAX_MSG_BYTES];
  uint8_t data_out_buf[HMAC_CMD_MAX_MSG_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  size_t status;
  // Pad with zeros
  memset(data_in_buf, 0, HMAC_CMD_MAX_MSG_BYTES);
  memcpy(data_in_buf, uj_input.data, uj_input.data_len);
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_hmac(data_in_buf, uj_input.data_len, key,
                               uj_input.key_len, data_out_buf, &data_out_len,
                               uj_input.padding, uj_input.mode, uj_input.cfg,
                               &cfg_out, &status, uj_input.trigger));
    // Copy output to input
    memset(data_in_buf, 0, HMAC_CMD_MAX_MSG_BYTES);
    memcpy(data_in_buf, data_out_buf, uj_input.data_len);
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_hmac_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.data, data_out_buf, HMAC_CMD_MAX_TAG_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_hmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_drbg_generate_batch(ujson_t *uj) {
  cryptolib_sca_sym_drbg_generate_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_drbg_generate_in_t(uj, &uj_input));

  // Invoke DRBG for each data set.
  uint8_t data_out_buf[DRBG_CMD_MAX_OUTPUT_BYTES];
  uint8_t nonce[DRBG_CMD_MAX_NONCE_BYTES];
  size_t cfg_out;
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    prng_rand_bytes(nonce, uj_input.nonce_len);
    TRY(trigger_cryptolib_drbg_generate(
        nonce, uj_input.nonce_len, data_out_buf, uj_input.data_len,
        uj_input.mode, uj_input.cfg, &cfg_out, &status, uj_input.trigger));
  }

  // Send the last data_out to host via UART.
  cryptolib_sca_sym_drbg_generate_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memset(uj_output.data, 0, DRBG_CMD_MAX_OUTPUT_BYTES);
  memcpy(uj_output.data, data_out_buf, uj_input.data_len);
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_drbg_generate_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_drbg_reseed(ujson_t *uj) {
  cryptolib_sca_sym_drbg_reseed_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_sym_drbg_reseed_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a DRBG reseed encryption.
  // Triggers are over the API calls.
  size_t cfg_out;
  status_t status = cryptolib_sca_drbg_reseed_impl(
      uj_input.entropy, uj_input.entropy_len, uj_input.nonce,
      uj_input.nonce_len, uj_input.reseed_interval, uj_input.mode, uj_input.cfg,
      &cfg_out, uj_input.trigger);

  /////////////// STUB END ///////////////

  cryptolib_sca_sym_drbg_reseed_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  uj_output.cfg = cfg_out;
  uj_output.status = (size_t)status.value;
  RESP_OK(ujson_serialize_cryptolib_sca_sym_drbg_reseed_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_sym_init(ujson_t *uj) {
  penetrationtest_cpuctrl_t uj_cpuctrl_data;
  TRY(ujson_deserialize_penetrationtest_cpuctrl_t(uj, &uj_cpuctrl_data));
  penetrationtest_sensor_config_t uj_sensor_data;
  TRY(ujson_deserialize_penetrationtest_sensor_config_t(uj, &uj_sensor_data));

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

  // Read different SKU config fields and return to host.
  TRY(pentest_send_sku_config(uj));

  /////////////// STUB START ///////////////
  uint32_t version;
  bool released;
  uint32_t build_hash_low;
  uint32_t build_hash_high;
  TRY(otcrypto_build_info(&version, &released, &build_hash_low,
                          &build_hash_high));
  char cryptolib_version[150];
  memset(cryptolib_version, '\0', sizeof(cryptolib_version));
  base_snprintf(cryptolib_version, sizeof(cryptolib_version),
                "CRYPTO version %08x, released %s, hash %08x%08x", version,
                released ? "true" : "false", build_hash_high, build_hash_low);
  RESP_OK(ujson_serialize_string, uj, cryptolib_version);

  // Check the security config of the device.
  TRY(otcrypto_security_config_check(kOtcryptoKeySecurityLevelHigh));
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
    case kCryptoLibScaSymSubcommandAesDaisy:
      return handle_cryptolib_sca_sym_aes_daisy_chain(uj);
    case kCryptoLibScaSymSubcommandCmacFvsrPlaintext:
      return handle_cryptolib_sca_sym_cmac_fvsr_plaintext(uj);
    case kCryptoLibScaSymSubcommandCmacFvsrKey:
      return handle_cryptolib_sca_sym_cmac_fvsr_key(uj);
    case kCryptoLibScaSymSubcommandCmacDaisy:
      return handle_cryptolib_sca_sym_cmac_daisy_chain(uj);
    case kCryptoLibScaSymSubcommandGcmFvsrPlaintext:
      return handle_cryptolib_sca_sym_gcm_fvsr_plaintext(uj);
    case kCryptoLibScaSymSubcommandGcmFvsrKey:
      return handle_cryptolib_sca_sym_gcm_fvsr_key(uj);
    case kCryptoLibScaSymSubcommandGcmDaisy:
      return handle_cryptolib_sca_sym_gcm_daisy_chain(uj);
    case kCryptoLibScaSymSubcommandTdesFvsrPlaintext:
      return handle_cryptolib_sca_sym_tdes_fvsr_plaintext(uj);
    case kCryptoLibScaSymSubcommandTdesFvsrKey:
      return handle_cryptolib_sca_sym_tdes_fvsr_key(uj);
    case kCryptoLibScaSymSubcommandTdesDaisy:
      return handle_cryptolib_sca_sym_tdes_daisy_chain(uj);
    case kCryptoLibScaSymSubcommandHmacFvsrPlaintext:
      return handle_cryptolib_sca_sym_hmac_fvsr_plaintext(uj);
    case kCryptoLibScaSymSubcommandHmacFvsrKey:
      return handle_cryptolib_sca_sym_hmac_fvsr_key(uj);
    case kCryptoLibScaSymSubcommandHmacDaisy:
      return handle_cryptolib_sca_sym_hmac_daisy_chain(uj);
    case kCryptoLibScaSymSubcommandDrbgGenerateBatch:
      return handle_cryptolib_sca_sym_drbg_generate_batch(uj);
    case kCryptoLibScaSymSubcommandDrbgReseed:
      return handle_cryptolib_sca_sym_drbg_reseed(uj);
    case kCryptoLibScaSymSubcommandInit:
      return handle_cryptolib_sca_sym_init(uj);
    default:
      LOG_ERROR("Unrecognized CryptoLib SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
