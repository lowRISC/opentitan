// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/cryptolib_sca_asym.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/security_config.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/firmware/sca/cryptolib_sca_asym_impl.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_sca_asym_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

status_t trigger_cryptolib_sca_asym_rsa_dec(
    uint8_t data[RSA_CMD_MAX_MESSAGE_BYTES], size_t data_len, size_t mode,
    uint8_t n[RSA_CMD_MAX_N_BYTES], uint8_t d[RSA_CMD_MAX_N_BYTES],
    size_t *n_len, uint8_t data_out[RSA_CMD_MAX_MESSAGE_BYTES],
    size_t *data_out_len, size_t hashing, size_t padding, size_t cfg_in,
    size_t *cfg_out, size_t *status, size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform an RSA decryption.
  // Adjust the hashing and the padding mode.
  // Triggers are over the API calls.
  *status = (size_t)cryptolib_sca_rsa_dec_impl(
                data, data_len, mode, n, d, n_len, data_out, data_out_len,
                hashing, padding, cfg_in, cfg_out, trigger)
                .value;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_rsa_dec(ujson_t *uj) {
  cryptolib_sca_asym_rsa_dec_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_rsa_dec_in_t(uj, &uj_input));

  uint8_t datain[RSA_CMD_MAX_MESSAGE_BYTES];
  memcpy(datain, uj_input.data, uj_input.data_len);
  uint8_t data_out_buf[RSA_CMD_MAX_MESSAGE_BYTES];
  size_t data_out_len;
  size_t cfg_out;
  size_t status;
  uint8_t n[RSA_CMD_MAX_N_BYTES];
  uint8_t d[RSA_CMD_MAX_N_BYTES];
  size_t n_len = uj_input.n_len;
  memset(n, 0, RSA_CMD_MAX_N_BYTES);
  memcpy(n, uj_input.n, n_len);
  memset(d, 0, RSA_CMD_MAX_N_BYTES);
  memcpy(d, uj_input.d, n_len);
  TRY(trigger_cryptolib_sca_asym_rsa_dec(
      datain, uj_input.data_len, uj_input.mode, n, d, &n_len, data_out_buf,
      &data_out_len, uj_input.hashing, uj_input.padding, uj_input.cfg, &cfg_out,
      &status, uj_input.trigger));

  // Send the last data_out to host via UART.
  cryptolib_sca_asym_rsa_dec_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.n, n, RSA_CMD_MAX_N_BYTES);
  memcpy(uj_output.d, d, RSA_CMD_MAX_N_BYTES);
  uj_output.n_len = n_len;
  memcpy(uj_output.data, data_out_buf, RSA_CMD_MAX_MESSAGE_BYTES);
  uj_output.data_len = data_out_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_asym_rsa_dec_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t trigger_cryptolib_sca_asym_rsa_sign(
    uint8_t data[RSA_CMD_MAX_MESSAGE_BYTES], size_t data_len,
    uint8_t n[RSA_CMD_MAX_N_BYTES], uint8_t d[RSA_CMD_MAX_N_BYTES],
    size_t *n_len, uint8_t sig[RSA_CMD_MAX_SIGNATURE_BYTES], size_t *sig_len,
    size_t hashing, size_t padding, size_t cfg_in, size_t *cfg_out,
    size_t *status, size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform an RSA sign.
  // Adjust the hashing and the padding mode.
  // Triggers are over the API calls.
  *status = (size_t)cryptolib_sca_rsa_sign_impl(data, data_len, n, d, n_len,
                                                sig, sig_len, hashing, padding,
                                                cfg_in, cfg_out, trigger)
                .value;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_prime(ujson_t *uj) {
  cryptolib_sca_asym_prime_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_prime_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Generates a prime.
  // Triggers are over the API calls.

  cryptolib_sca_asym_prime_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_asym_prime_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_rsa_sign(ujson_t *uj) {
  cryptolib_sca_asym_rsa_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_rsa_sign_in_t(uj, &uj_input));

  uint8_t data_in_buf[RSA_CMD_MAX_MESSAGE_BYTES];
  uint8_t sig_buf[RSA_CMD_MAX_SIGNATURE_BYTES];
  size_t sig_len;
  uint8_t n[RSA_CMD_MAX_N_BYTES];
  uint8_t d[RSA_CMD_MAX_N_BYTES];
  size_t n_len = uj_input.n_len;
  memset(n, 0, RSA_CMD_MAX_N_BYTES);
  memcpy(n, uj_input.n, n_len);
  memset(d, 0, RSA_CMD_MAX_N_BYTES);
  memcpy(d, uj_input.d, n_len);
  memset(data_in_buf, 0, RSA_CMD_MAX_MESSAGE_BYTES);
  memcpy(data_in_buf, uj_input.data, uj_input.data_len);
  size_t cfg_out;
  size_t status;
  TRY(trigger_cryptolib_sca_asym_rsa_sign(
      data_in_buf, uj_input.data_len, n, d, &n_len, sig_buf, &sig_len,
      uj_input.hashing, uj_input.padding, uj_input.cfg, &cfg_out, &status,
      uj_input.trigger));

  cryptolib_sca_asym_rsa_sign_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.n, n, RSA_CMD_MAX_N_BYTES);
  memcpy(uj_output.d, d, RSA_CMD_MAX_N_BYTES);
  uj_output.n_len = n_len;
  memcpy(uj_output.sig, sig_buf, RSA_CMD_MAX_SIGNATURE_BYTES);
  uj_output.sig_len = sig_len;
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_asym_rsa_sign_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t trigger_cryptolib_sca_asym_p256_base_mul(
    uint8_t scalar[P256_CMD_BYTES], uint8_t x[P256_CMD_BYTES],
    uint8_t y[P256_CMD_BYTES], size_t cfg_in, size_t *cfg_out, size_t *status,
    size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a base point multiplication in P256.
  // Trigger are over the API calls.

  memset(x, 0, P256_CMD_BYTES);
  memset(y, 0, P256_CMD_BYTES);
  *cfg_out = 0;
  *status = 0;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_p256_base_mul_fvsr(ujson_t *uj) {
  cryptolib_sca_asym_p256_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_p256_base_mul_in_t(uj, &uj_input));

  uint8_t batch_scalar[uj_input.num_iterations][P256_CMD_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided data is used. When
  // not sample_fixed, random data is generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_scalar[it], uj_input.scalar, P256_CMD_BYTES);
    } else {
      prng_rand_bytes(batch_scalar[it], P256_CMD_BYTES);
    }
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke point mul for each data set.
  uint8_t x[P256_CMD_BYTES];
  uint8_t y[P256_CMD_BYTES];
  size_t cfg_out;
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_sca_asym_p256_base_mul(batch_scalar[it], x, y,
                                                 uj_input.cfg, &cfg_out,
                                                 &status, uj_input.trigger));
  }

  // Send the last coordinates to host via UART.
  cryptolib_sca_asym_p256_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.x, x, P256_CMD_BYTES);
  memcpy(uj_output.y, y, P256_CMD_BYTES);
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_asym_p256_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_p256_base_mul_daisy_chaining(ujson_t *uj) {
  cryptolib_sca_asym_p256_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_p256_base_mul_in_t(uj, &uj_input));

  // Invoke point mul for each data set.
  uint8_t scalar[P256_CMD_BYTES];
  uint8_t x[P256_CMD_BYTES];
  uint8_t y[P256_CMD_BYTES];
  memset(scalar, 0, P256_CMD_BYTES);
  memcpy(scalar, uj_input.scalar, P256_CMD_BYTES);
  size_t cfg_out;
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_sca_asym_p256_base_mul(
        scalar, x, y, uj_input.cfg, &cfg_out, &status, uj_input.trigger));

    // Copy out x coordinate to scalar
    memset(scalar, 0, P256_CMD_BYTES);
    memcpy(scalar, x, P256_CMD_BYTES);
  }

  // Send the last coordinates to host via UART.
  cryptolib_sca_asym_p256_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.x, x, P256_CMD_BYTES);
  memcpy(uj_output.y, y, P256_CMD_BYTES);
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_asym_p256_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_p256_point_mul(ujson_t *uj) {
  cryptolib_sca_asym_p256_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_p256_point_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in P256.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  cryptolib_sca_asym_p256_point_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_asym_p256_point_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_p256_ecdh(ujson_t *uj) {
  cryptolib_sca_asym_p256_ecdh_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_p256_ecdh_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform ECDH in P256.
  // Trigger are over the API calls.
  cryptolib_sca_asym_p256_ecdh_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  uj_output.status =
      (size_t)cryptolib_sca_p256_ecdh_impl(uj_input, &uj_output).value;
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_sca_asym_p256_ecdh_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_p256_sign(ujson_t *uj) {
  cryptolib_sca_asym_p256_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_p256_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a P256 signature.
  // Trigger are over the API calls.
  cryptolib_sca_asym_p256_sign_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  uj_output.status =
      (size_t)cryptolib_sca_p256_sign_impl(uj_input, &uj_output).value;
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_sca_asym_p256_sign_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t trigger_cryptolib_sca_asym_p384_base_mul(
    uint8_t scalar[P384_CMD_BYTES], uint8_t x[P384_CMD_BYTES],
    uint8_t y[P384_CMD_BYTES], size_t cfg_in, size_t *cfg_out, size_t *status,
    size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a base point multiplication in p384.
  // Trigger are over the API calls.

  memset(x, 0, P384_CMD_BYTES);
  memset(y, 0, P384_CMD_BYTES);
  *cfg_out = 0;
  *status = 0;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_p384_base_mul_fvsr(ujson_t *uj) {
  cryptolib_sca_asym_p384_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_p384_base_mul_in_t(uj, &uj_input));

  uint8_t batch_scalar[uj_input.num_iterations][P384_CMD_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided data is used. When
  // not sample_fixed, random data is generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_scalar[it], uj_input.scalar, P384_CMD_BYTES);
    } else {
      prng_rand_bytes(batch_scalar[it], P384_CMD_BYTES);
    }
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke point mul for each data set.
  uint8_t x[P384_CMD_BYTES];
  uint8_t y[P384_CMD_BYTES];
  size_t cfg_out;
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_sca_asym_p384_base_mul(batch_scalar[it], x, y,
                                                 uj_input.cfg, &cfg_out,
                                                 &status, uj_input.trigger));
  }

  // Send the last coordinates to host via UART.
  cryptolib_sca_asym_p384_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.x, x, P384_CMD_BYTES);
  memcpy(uj_output.y, y, P384_CMD_BYTES);
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_asym_p384_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_p384_base_mul_daisy_chaining(ujson_t *uj) {
  cryptolib_sca_asym_p384_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_p384_base_mul_in_t(uj, &uj_input));

  // Invoke point mul for each data set.
  uint8_t scalar[P384_CMD_BYTES];
  uint8_t x[P384_CMD_BYTES];
  uint8_t y[P384_CMD_BYTES];
  memset(scalar, 0, P384_CMD_BYTES);
  memcpy(scalar, uj_input.scalar, P384_CMD_BYTES);
  size_t cfg_out;
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_sca_asym_p384_base_mul(
        scalar, x, y, uj_input.cfg, &cfg_out, &status, uj_input.trigger));
    // Copy out x coordinate to scalar
    memset(scalar, 0, P384_CMD_BYTES);
    memcpy(scalar, x, P384_CMD_BYTES);
  }

  // Send the last coordinates to host via UART.
  cryptolib_sca_asym_p384_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.x, x, P384_CMD_BYTES);
  memcpy(uj_output.y, y, P384_CMD_BYTES);
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_asym_p384_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_p384_point_mul(ujson_t *uj) {
  cryptolib_sca_asym_p384_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_p384_point_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in p384.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  cryptolib_sca_asym_p384_point_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_asym_p384_point_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_p384_ecdh(ujson_t *uj) {
  cryptolib_sca_asym_p384_ecdh_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_p384_ecdh_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform ECDH in P384.
  // Trigger are over the API calls.
  cryptolib_sca_asym_p384_ecdh_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  uj_output.status =
      (size_t)cryptolib_sca_p384_ecdh_impl(uj_input, &uj_output).value;
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_sca_asym_p384_ecdh_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_p384_sign(ujson_t *uj) {
  cryptolib_sca_asym_p384_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_p384_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a p384 signature.
  // Trigger are over the API calls.
  cryptolib_sca_asym_p384_sign_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  uj_output.status =
      (size_t)cryptolib_sca_p384_sign_impl(uj_input, &uj_output).value;
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_sca_asym_p384_sign_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t trigger_cryptolib_sca_asym_secp256k1_base_mul(
    uint8_t scalar[SECP256K1_CMD_BYTES], uint8_t x[SECP256K1_CMD_BYTES],
    uint8_t y[SECP256K1_CMD_BYTES], size_t cfg_in, size_t *cfg_out,
    size_t *status, size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a base point multiplication in secp256k1.
  // Trigger are over the API calls.

  memset(x, 0, SECP256K1_CMD_BYTES);
  memset(y, 0, SECP256K1_CMD_BYTES);
  *cfg_out = 0;
  *status = 0;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_secp256k1_base_mul_fvsr(ujson_t *uj) {
  cryptolib_sca_asym_secp256k1_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_secp256k1_base_mul_in_t(uj,
                                                                   &uj_input));

  uint8_t batch_scalar[uj_input.num_iterations][SECP256K1_CMD_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided data is used. When
  // not sample_fixed, random data is generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_scalar[it], uj_input.scalar, SECP256K1_CMD_BYTES);
    } else {
      prng_rand_bytes(batch_scalar[it], SECP256K1_CMD_BYTES);
    }
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke point mul for each data set.
  uint8_t x[SECP256K1_CMD_BYTES];
  uint8_t y[SECP256K1_CMD_BYTES];
  size_t cfg_out;
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_sca_asym_secp256k1_base_mul(
        batch_scalar[it], x, y, uj_input.cfg, &cfg_out, &status,
        uj_input.trigger));
  }

  // Send the last coordinates to host via UART.
  cryptolib_sca_asym_secp256k1_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.x, x, SECP256K1_CMD_BYTES);
  memcpy(uj_output.y, y, SECP256K1_CMD_BYTES);
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_asym_secp256k1_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_secp256k1_base_mul_daisy_chaining(
    ujson_t *uj) {
  cryptolib_sca_asym_secp256k1_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_secp256k1_base_mul_in_t(uj,
                                                                   &uj_input));

  // Invoke point mul for each data set.
  uint8_t scalar[SECP256K1_CMD_BYTES];
  uint8_t x[SECP256K1_CMD_BYTES];
  uint8_t y[SECP256K1_CMD_BYTES];
  memset(scalar, 0, SECP256K1_CMD_BYTES);
  memcpy(scalar, uj_input.scalar, SECP256K1_CMD_BYTES);
  size_t cfg_out;
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_sca_asym_secp256k1_base_mul(
        scalar, x, y, uj_input.cfg, &cfg_out, &status, uj_input.trigger));
    // Copy out x coordinate to scalar
    memset(scalar, 0, SECP256K1_CMD_BYTES);
    memcpy(scalar, x, SECP256K1_CMD_BYTES);
  }

  // Send the last coordinates to host via UART.
  cryptolib_sca_asym_secp256k1_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.x, x, SECP256K1_CMD_BYTES);
  memcpy(uj_output.y, y, SECP256K1_CMD_BYTES);
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_asym_secp256k1_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_secp256k1_point_mul(ujson_t *uj) {
  cryptolib_sca_asym_secp256k1_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_secp256k1_point_mul_in_t(uj,
                                                                    &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in secp256k1.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  cryptolib_sca_asym_secp256k1_point_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_asym_secp256k1_point_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_secp256k1_ecdh(ujson_t *uj) {
  cryptolib_sca_asym_secp256k1_ecdh_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_secp256k1_ecdh_in_t(uj, &uj_input));
  /////////////// STUB START ///////////////
  // Perform ECDH in secp256k1.
  // Trigger are over the API calls.

  cryptolib_sca_asym_secp256k1_ecdh_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_asym_secp256k1_ecdh_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_secp256k1_sign(ujson_t *uj) {
  cryptolib_sca_asym_secp256k1_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_secp256k1_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a secp256k1 signature.
  // Trigger are over the API calls.

  cryptolib_sca_asym_secp256k1_sign_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_asym_secp256k1_sign_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t trigger_cryptolib_sca_asym_x25519_base_mul(
    uint8_t scalar[X25519_CMD_BYTES], uint8_t x[X25519_CMD_BYTES],
    uint8_t y[X25519_CMD_BYTES], size_t cfg_in, size_t *cfg_out, size_t *status,
    size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a base point multiplication in X25519.
  // Trigger are over the API calls.

  memset(x, 0, X25519_CMD_BYTES);
  memset(y, 0, X25519_CMD_BYTES);
  *cfg_out = 0;
  *status = 0;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_x25519_base_mul_fvsr(ujson_t *uj) {
  cryptolib_sca_asym_x25519_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_x25519_base_mul_in_t(uj, &uj_input));

  uint8_t batch_scalar[uj_input.num_iterations][X25519_CMD_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided data is used. When
  // not sample_fixed, random data is generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_scalar[it], uj_input.scalar, X25519_CMD_BYTES);
    } else {
      prng_rand_bytes(batch_scalar[it], X25519_CMD_BYTES);
    }
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke point mul for each data set.
  uint8_t x[X25519_CMD_BYTES];
  uint8_t y[X25519_CMD_BYTES];
  size_t cfg_out;
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_sca_asym_x25519_base_mul(batch_scalar[it], x, y,
                                                   uj_input.cfg, &cfg_out,
                                                   &status, uj_input.trigger));
  }

  // Send the last coordinates to host via UART.
  cryptolib_sca_asym_x25519_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.x, x, X25519_CMD_BYTES);
  memcpy(uj_output.y, y, X25519_CMD_BYTES);
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_asym_x25519_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_x25519_base_mul_daisy_chaining(ujson_t *uj) {
  cryptolib_sca_asym_x25519_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_x25519_base_mul_in_t(uj, &uj_input));

  // Invoke point mul for each data set.
  uint8_t scalar[X25519_CMD_BYTES];
  uint8_t x[X25519_CMD_BYTES];
  uint8_t y[X25519_CMD_BYTES];
  memset(scalar, 0, X25519_CMD_BYTES);
  memcpy(scalar, uj_input.scalar, X25519_CMD_BYTES);
  size_t cfg_out;
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_sca_asym_x25519_base_mul(
        scalar, x, y, uj_input.cfg, &cfg_out, &status, uj_input.trigger));
    // Copy out x coordinate to scalar
    memset(scalar, 0, X25519_CMD_BYTES);
    memcpy(scalar, x, X25519_CMD_BYTES);
  }

  // Send the last coordinates to host via UART.
  cryptolib_sca_asym_x25519_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.x, x, X25519_CMD_BYTES);
  memcpy(uj_output.y, y, X25519_CMD_BYTES);
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_asym_x25519_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_x25519_point_mul(ujson_t *uj) {
  cryptolib_sca_asym_x25519_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_x25519_point_mul_in_t(uj,
                                                                 &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in X25519.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  cryptolib_sca_asym_x25519_point_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_asym_x25519_point_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_x25519_ecdh(ujson_t *uj) {
  cryptolib_sca_asym_x25519_ecdh_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_x25519_ecdh_in_t(uj, &uj_input));
  /////////////// STUB START ///////////////
  // Perform ECDH in x25519.
  // Trigger are over the API calls.

  cryptolib_sca_asym_x25519_ecdh_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_asym_x25519_ecdh_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t trigger_cryptolib_sca_asym_ed25519_base_mul(
    uint8_t scalar[ED25519_CMD_SCALAR_BYTES],
    uint8_t x[ED25519_CMD_SCALAR_BYTES], uint8_t y[ED25519_CMD_SCALAR_BYTES],
    size_t cfg_in, size_t *cfg_out, size_t *status, size_t trigger) {
  /////////////// STUB START ///////////////
  // Perform a base point multiplication in ED25519.
  // Trigger are over the API calls.

  memset(x, 0, ED25519_CMD_SCALAR_BYTES);
  memset(y, 0, ED25519_CMD_SCALAR_BYTES);
  *cfg_out = 0;
  *status = 0;
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_ed25519_base_mul_fvsr(ujson_t *uj) {
  cryptolib_sca_asym_ed25519_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_ed25519_base_mul_in_t(uj,
                                                                 &uj_input));

  uint8_t batch_scalar[uj_input.num_iterations][ED25519_CMD_SCALAR_BYTES];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided data is used. When
  // not sample_fixed, random data is generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_scalar[it], uj_input.scalar, ED25519_CMD_SCALAR_BYTES);
    } else {
      prng_rand_bytes(batch_scalar[it], ED25519_CMD_SCALAR_BYTES);
    }
    sample_fixed = prng_rand_byte() & 0x1;
  }

  // Invoke point mul for each data set.
  uint8_t x[ED25519_CMD_SCALAR_BYTES];
  uint8_t y[ED25519_CMD_SCALAR_BYTES];
  size_t cfg_out;
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_sca_asym_ed25519_base_mul(batch_scalar[it], x, y,
                                                    uj_input.cfg, &cfg_out,
                                                    &status, uj_input.trigger));
  }

  // Send the last coordinates to host via UART.
  cryptolib_sca_asym_ed25519_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.x, x, ED25519_CMD_SCALAR_BYTES);
  memcpy(uj_output.y, y, ED25519_CMD_SCALAR_BYTES);
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_asym_ed25519_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_ed25519_base_mul_daisy_chaining(
    ujson_t *uj) {
  cryptolib_sca_asym_ed25519_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_ed25519_base_mul_in_t(uj,
                                                                 &uj_input));

  // Invoke point mul for each data set.
  uint8_t scalar[ED25519_CMD_SCALAR_BYTES];
  uint8_t x[ED25519_CMD_SCALAR_BYTES];
  uint8_t y[ED25519_CMD_SCALAR_BYTES];
  memset(scalar, 0, ED25519_CMD_SCALAR_BYTES);
  memcpy(scalar, uj_input.scalar, ED25519_CMD_SCALAR_BYTES);
  size_t cfg_out;
  size_t status;
  for (size_t it = 0; it < uj_input.num_iterations; it++) {
    TRY(trigger_cryptolib_sca_asym_ed25519_base_mul(
        scalar, x, y, uj_input.cfg, &cfg_out, &status, uj_input.trigger));
    // Copy out x coordinate to scalar
    memset(scalar, 0, ED25519_CMD_SCALAR_BYTES);
    memcpy(scalar, x, ED25519_CMD_SCALAR_BYTES);
  }

  // Send the last coordinates to host via UART.
  cryptolib_sca_asym_ed25519_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.x, x, ED25519_CMD_SCALAR_BYTES);
  memcpy(uj_output.y, y, ED25519_CMD_SCALAR_BYTES);
  uj_output.cfg = cfg_out;
  uj_output.status = status;
  RESP_OK(ujson_serialize_cryptolib_sca_asym_ed25519_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_ed25519_sign(ujson_t *uj) {
  cryptolib_sca_asym_ed25519_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_sca_asym_ed25519_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a ED25519 signature.
  // Trigger are over the API calls.

  cryptolib_sca_asym_ed25519_sign_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_sca_asym_ed25519_sign_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym_init(ujson_t *uj) {
  // Configure the device.
  pentest_setup_device(uj, false, false);

  pentest_select_trigger_type(kPentestTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // pentest_init is not needed. kPentestTriggerSourceAes is selected as a
  // placeholder.
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralEdn |
                   kPentestPeripheralCsrng | kPentestPeripheralEntropy |
                   kPentestPeripheralAes | kPentestPeripheralHmac |
                   kPentestPeripheralKmac | kPentestPeripheralOtbn);

  /////////////// STUB START ///////////////
  // Add things like versioning.

  // Check the security config of the device.
  TRY(otcrypto_security_config_check(kOtcryptoKeySecurityLevelHigh));
  /////////////// STUB END ///////////////

  return OK_STATUS();
}

status_t handle_cryptolib_sca_asym(ujson_t *uj) {
  cryptolib_sca_asym_subcommand_t cmd;
  TRY(ujson_deserialize_cryptolib_sca_asym_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kCryptoLibScaAsymSubcommandRsaDec:
      return handle_cryptolib_sca_asym_rsa_dec(uj);
    case kCryptoLibScaAsymSubcommandRsaSign:
      return handle_cryptolib_sca_asym_rsa_sign(uj);
    case kCryptoLibScaAsymSubcommandPrime:
      return handle_cryptolib_sca_asym_prime(uj);
    case kCryptoLibScaAsymSubcommandP256BaseMulFvsr:
      return handle_cryptolib_sca_asym_p256_base_mul_fvsr(uj);
    case kCryptoLibScaAsymSubcommandP256BaseMulDaisy:
      return handle_cryptolib_sca_asym_p256_base_mul_daisy_chaining(uj);
    case kCryptoLibScaAsymSubcommandP256PointMul:
      return handle_cryptolib_sca_asym_p256_point_mul(uj);
    case kCryptoLibScaAsymSubcommandP256Ecdh:
      return handle_cryptolib_sca_asym_p256_ecdh(uj);
    case kCryptoLibScaAsymSubcommandP256Sign:
      return handle_cryptolib_sca_asym_p256_sign(uj);
    case kCryptoLibScaAsymSubcommandP384BaseMulFvsr:
      return handle_cryptolib_sca_asym_p384_base_mul_fvsr(uj);
    case kCryptoLibScaAsymSubcommandP384BaseMulDaisy:
      return handle_cryptolib_sca_asym_p384_base_mul_daisy_chaining(uj);
    case kCryptoLibScaAsymSubcommandP384PointMul:
      return handle_cryptolib_sca_asym_p384_point_mul(uj);
    case kCryptoLibScaAsymSubcommandP384Ecdh:
      return handle_cryptolib_sca_asym_p384_ecdh(uj);
    case kCryptoLibScaAsymSubcommandP384Sign:
      return handle_cryptolib_sca_asym_p384_sign(uj);
    case kCryptoLibScaAsymSubcommandSecp256k1BaseMulFvsr:
      return handle_cryptolib_sca_asym_secp256k1_base_mul_fvsr(uj);
    case kCryptoLibScaAsymSubcommandSecp256k1BaseMulDaisy:
      return handle_cryptolib_sca_asym_secp256k1_base_mul_daisy_chaining(uj);
    case kCryptoLibScaAsymSubcommandSecp256k1PointMul:
      return handle_cryptolib_sca_asym_secp256k1_point_mul(uj);
    case kCryptoLibScaAsymSubcommandSecp256k1Ecdh:
      return handle_cryptolib_sca_asym_secp256k1_ecdh(uj);
    case kCryptoLibScaAsymSubcommandSecp256k1Sign:
      return handle_cryptolib_sca_asym_secp256k1_sign(uj);
    case kCryptoLibScaAsymSubcommandX25519BaseMulFvsr:
      return handle_cryptolib_sca_asym_x25519_base_mul_fvsr(uj);
    case kCryptoLibScaAsymSubcommandX25519BaseMulDaisy:
      return handle_cryptolib_sca_asym_x25519_base_mul_daisy_chaining(uj);
    case kCryptoLibScaAsymSubcommandX25519PointMul:
      return handle_cryptolib_sca_asym_x25519_point_mul(uj);
    case kCryptoLibScaAsymSubcommandX25519Ecdh:
      return handle_cryptolib_sca_asym_x25519_ecdh(uj);
    case kCryptoLibScaAsymSubcommandEd25519BaseMulFvsr:
      return handle_cryptolib_sca_asym_ed25519_base_mul_fvsr(uj);
    case kCryptoLibScaAsymSubcommandEd25519BaseMulDaisy:
      return handle_cryptolib_sca_asym_ed25519_base_mul_daisy_chaining(uj);
    case kCryptoLibScaAsymSubcommandEd25519Sign:
      return handle_cryptolib_sca_asym_ed25519_sign(uj);
    case kCryptoLibScaAsymSubcommandInit:
      return handle_cryptolib_sca_asym_init(uj);
    default:
      LOG_ERROR("Unrecognized CryptoLib SCA ASYM subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
