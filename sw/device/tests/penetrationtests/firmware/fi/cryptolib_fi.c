// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/cryptolib_fi.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

status_t handle_cryptolib_fi_aes(ujson_t *uj) {
  cryptolib_fi_aes_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_aes_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform an AES encryption or decryption.
  // Adjust the mode of operation and the padding mode.
  // The total size of this test can be large due to all these options.
  // Triggers are over the API calls.

  cryptolib_fi_aes_out_t uj_output;
  memset(uj_output.data, 0, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = AES_CMD_MAX_MSG_BYTES;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_aes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_cmac(ujson_t *uj) {
  cryptolib_fi_cmac_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_cmac_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a CMAC encryption.
  // Verify the tag before sending the output.
  // Triggers are over the API calls.

  cryptolib_fi_cmac_out_t uj_output;
  memset(uj_output.data, 0, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = AES_CMD_MAX_MSG_BYTES;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_cmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_gcm(ujson_t *uj) {
  cryptolib_fi_gcm_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_gcm_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a GCM encryption with aad and generate a tag.
  // Then, verify that tag again, before sending the output.
  // Trigger are over the API calls.

  cryptolib_fi_gcm_out_t uj_output;
  memset(uj_output.data, 0, AES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = AES_CMD_MAX_MSG_BYTES;
  memset(uj_output.tag, 0, AES_CMD_MAX_MSG_BYTES);
  uj_output.tag_len = AES_CMD_MAX_MSG_BYTES;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_gcm_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_tdes(ujson_t *uj) {
  cryptolib_fi_tdes_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_tdes_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a TDES encryption or decryption.
  // Adjust the mode of operation and the padding mode.
  // Triggers are over the API calls.

  cryptolib_fi_tdes_out_t uj_output;
  memset(uj_output.data, 0, TDES_CMD_MAX_MSG_BYTES);
  uj_output.data_len = TDES_CMD_MAX_MSG_BYTES;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_tdes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_hmac(ujson_t *uj) {
  cryptolib_fi_hmac_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_hmac_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform an HMAC call.
  // Trigger are over the API calls.

  cryptolib_fi_hmac_out_t uj_output;
  memset(uj_output.data, 0, HMAC_CMD_MAX_MSG_BYTES);
  uj_output.data_len = HMAC_CMD_MAX_MSG_BYTES;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_hmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_drbg(ujson_t *uj) {
  cryptolib_fi_drbg_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_drbg_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a DRBG call to generate random output.
  // Trigger are over the API calls.

  cryptolib_fi_drbg_out_t uj_output;
  memset(uj_output.data, 0, DRBG_CMD_MAX_OUTPUT_BYTES);
  uj_output.data_len = DRBG_CMD_MAX_OUTPUT_BYTES;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_drbg_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_rsa_enc(ujson_t *uj) {
  cryptolib_fi_rsa_enc_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_rsa_enc_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform an RSA encryption with hashing and padding options.
  // You can give cfg a value such that the RSA generates its own private key.
  // Trigger are over the API calls.

  cryptolib_fi_rsa_enc_out_t uj_output;
  memset(uj_output.data, 0, RSA_CMD_MAX_MESSAGE_BYTES);
  uj_output.data_len = RSA_CMD_MAX_MESSAGE_BYTES;
  memset(uj_output.n, 0, RSA_CMD_MAX_N_BYTES);
  memset(uj_output.d, 0, RSA_CMD_MAX_N_BYTES);
  uj_output.n_len = RSA_CMD_MAX_N_BYTES;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_rsa_enc_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_rsa_sign(ujson_t *uj) {
  cryptolib_fi_rsa_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_rsa_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform an RSA signing with hashing and padding options.
  // You can give cfg a value such that the RSA generates its own private key
  // and you can give a value such that RSA switches between signing and
  // verifying against the given signature. Trigger are over the API calls.

  cryptolib_fi_rsa_sign_out_t uj_output;
  memset(uj_output.sig, 0, RSA_CMD_MAX_SIGNATURE_BYTES);
  uj_output.sig_len = RSA_CMD_MAX_SIGNATURE_BYTES;
  memset(uj_output.n, 0, RSA_CMD_MAX_N_BYTES);
  memset(uj_output.d, 0, RSA_CMD_MAX_N_BYTES);
  uj_output.n_len = RSA_CMD_MAX_N_BYTES;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_rsa_sign_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_prime(ujson_t *uj) {
  cryptolib_fi_prime_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_prime_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Generate a prime.
  // Trigger are over the API calls.

  cryptolib_fi_prime_out_t uj_output;
  memset(uj_output.prime, 0, RSA_CMD_MAX_MESSAGE_BYTES);
  uj_output.prime_len = RSA_CMD_MAX_MESSAGE_BYTES;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_prime_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_p256_base_mul(ujson_t *uj) {
  cryptolib_fi_p256_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_p256_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in P256.
  // Trigger are over the API calls.

  cryptolib_fi_p256_base_mul_out_t uj_output;
  memset(uj_output.x, 0, P256_CMD_BYTES);
  memset(uj_output.y, 0, P256_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_p256_base_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_p256_point_mul(ujson_t *uj) {
  cryptolib_fi_p256_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_p256_point_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in P256.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  cryptolib_fi_p256_point_mul_out_t uj_output;
  memset(uj_output.x, 0, P256_CMD_BYTES);
  memset(uj_output.y, 0, P256_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_p256_point_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_p256_sign(ujson_t *uj) {
  cryptolib_fi_p256_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_p256_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a P256 signature.
  // Trigger are over the API calls.

  cryptolib_fi_p256_sign_out_t uj_output;
  memset(uj_output.pubx, 0, P256_CMD_BYTES);
  memset(uj_output.puby, 0, P256_CMD_BYTES);
  memset(uj_output.r, 0, P256_CMD_BYTES);
  memset(uj_output.s, 0, P256_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_p256_sign_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_p256_verify(ujson_t *uj) {
  cryptolib_fi_p256_verify_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_p256_verify_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a P256 verification.
  // Trigger are over the API calls.

  cryptolib_fi_p256_verify_out_t uj_output;
  uj_output.result = true;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_p256_verify_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_p384_base_mul(ujson_t *uj) {
  cryptolib_fi_p384_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_p384_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in p384.
  // Trigger are over the API calls.

  cryptolib_fi_p384_base_mul_out_t uj_output;
  memset(uj_output.x, 0, P384_CMD_BYTES);
  memset(uj_output.y, 0, P384_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_p384_base_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_p384_point_mul(ujson_t *uj) {
  cryptolib_fi_p384_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_p384_point_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in p384.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  cryptolib_fi_p384_point_mul_out_t uj_output;
  memset(uj_output.x, 0, P384_CMD_BYTES);
  memset(uj_output.y, 0, P384_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_p384_point_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_p384_sign(ujson_t *uj) {
  cryptolib_fi_p384_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_p384_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a p384 signature.
  // Trigger are over the API calls.

  cryptolib_fi_p384_sign_out_t uj_output;
  memset(uj_output.pubx, 0, P384_CMD_BYTES);
  memset(uj_output.puby, 0, P384_CMD_BYTES);
  memset(uj_output.r, 0, P384_CMD_BYTES);
  memset(uj_output.s, 0, P384_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_p384_sign_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_p384_verify(ujson_t *uj) {
  cryptolib_fi_p384_verify_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_p384_verify_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a p384 verification.
  // Trigger are over the API calls.

  cryptolib_fi_p384_verify_out_t uj_output;
  uj_output.result = true;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_p384_verify_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_secp256k1_base_mul(ujson_t *uj) {
  cryptolib_fi_secp256k1_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_secp256k1_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in secp256k1.
  // Trigger are over the API calls.

  cryptolib_fi_secp256k1_base_mul_out_t uj_output;
  memset(uj_output.x, 0, SECP256K1_CMD_BYTES);
  memset(uj_output.y, 0, SECP256K1_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_secp256k1_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_secp256k1_point_mul(ujson_t *uj) {
  cryptolib_fi_secp256k1_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_secp256k1_point_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in secp256k1.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  cryptolib_fi_secp256k1_point_mul_out_t uj_output;
  memset(uj_output.x, 0, SECP256K1_CMD_BYTES);
  memset(uj_output.y, 0, SECP256K1_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_secp256k1_point_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_secp256k1_sign(ujson_t *uj) {
  cryptolib_fi_secp256k1_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_secp256k1_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a secp256k1 signature.
  // Trigger are over the API calls.

  cryptolib_fi_secp256k1_sign_out_t uj_output;
  memset(uj_output.pubx, 0, SECP256K1_CMD_BYTES);
  memset(uj_output.puby, 0, SECP256K1_CMD_BYTES);
  memset(uj_output.r, 0, SECP256K1_CMD_BYTES);
  memset(uj_output.s, 0, SECP256K1_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_secp256k1_sign_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_secp256k1_verify(ujson_t *uj) {
  cryptolib_fi_secp256k1_verify_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_secp256k1_verify_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a secp256k1 verification.
  // Trigger are over the API calls.

  cryptolib_fi_secp256k1_verify_out_t uj_output;
  uj_output.result = true;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_secp256k1_verify_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_x25519_base_mul(ujson_t *uj) {
  cryptolib_fi_x25519_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_x25519_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in X25519.
  // Trigger are over the API calls.

  cryptolib_fi_x25519_base_mul_out_t uj_output;
  memset(uj_output.x, 0, X25519_CMD_BYTES);
  memset(uj_output.y, 0, X25519_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_x25519_base_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_x25519_point_mul(ujson_t *uj) {
  cryptolib_fi_x25519_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_x25519_point_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in X25519.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  cryptolib_fi_x25519_point_mul_out_t uj_output;
  memset(uj_output.x, 0, X25519_CMD_BYTES);
  memset(uj_output.y, 0, X25519_CMD_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_x25519_point_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_ed25519_base_mul(ujson_t *uj) {
  cryptolib_fi_ed25519_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_ed25519_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in ED25519.
  // Trigger are over the API calls.

  cryptolib_fi_ed25519_base_mul_out_t uj_output;
  memset(uj_output.x, 0, ED25519_CMD_SCALAR_BYTES);
  memset(uj_output.y, 0, ED25519_CMD_SCALAR_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_ed25519_base_mul_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_ed25519_sign(ujson_t *uj) {
  cryptolib_fi_ed25519_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_ed25519_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a ED25519 signature.
  // Trigger are over the API calls.

  cryptolib_fi_ed25519_sign_out_t uj_output;
  memset(uj_output.pubx, 0, ED25519_CMD_SCALAR_BYTES);
  memset(uj_output.puby, 0, ED25519_CMD_SCALAR_BYTES);
  memset(uj_output.r, 0, ED25519_CMD_SIG_BYTES);
  memset(uj_output.s, 0, ED25519_CMD_SIG_BYTES);
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_ed25519_sign_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_ed25519_verify(ujson_t *uj) {
  cryptolib_fi_ed25519_verify_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_ed25519_verify_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a ED25519 verification.
  // Trigger are over the API calls.

  cryptolib_fi_ed25519_verify_out_t uj_output;
  uj_output.result = true;
  uj_output.cfg = 0;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_ed25519_verify_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_init(ujson_t *uj) {
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

status_t handle_cryptolib_fi(ujson_t *uj) {
  cryptolib_fi_subcommand_t cmd;
  TRY(ujson_deserialize_cryptolib_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kCryptoLibFiSubcommandAes:
      return handle_cryptolib_fi_aes(uj);
    case kCryptoLibFiSubcommandCmac:
      return handle_cryptolib_fi_cmac(uj);
    case kCryptoLibFiSubcommandGcm:
      return handle_cryptolib_fi_gcm(uj);
    case kCryptoLibFiSubcommandTdes:
      return handle_cryptolib_fi_tdes(uj);
    case kCryptoLibFiSubcommandHmac:
      return handle_cryptolib_fi_hmac(uj);
    case kCryptoLibFiSubcommandDrbg:
      return handle_cryptolib_fi_drbg(uj);
    case kCryptoLibFiSubcommandRsaEnc:
      return handle_cryptolib_fi_rsa_enc(uj);
    case kCryptoLibFiSubcommandRsaSign:
      return handle_cryptolib_fi_rsa_sign(uj);
    case kCryptoLibFiSubcommandPrime:
      return handle_cryptolib_fi_prime(uj);
    case kCryptoLibFiSubcommandP256BaseMul:
      return handle_cryptolib_fi_p256_base_mul(uj);
    case kCryptoLibFiSubcommandP256PointMul:
      return handle_cryptolib_fi_p256_point_mul(uj);
    case kCryptoLibFiSubcommandP256Sign:
      return handle_cryptolib_fi_p256_sign(uj);
    case kCryptoLibFiSubcommandP256Verify:
      return handle_cryptolib_fi_p256_verify(uj);
    case kCryptoLibFiSubcommandP384BaseMul:
      return handle_cryptolib_fi_p384_base_mul(uj);
    case kCryptoLibFiSubcommandP384PointMul:
      return handle_cryptolib_fi_p384_point_mul(uj);
    case kCryptoLibFiSubcommandP384Sign:
      return handle_cryptolib_fi_p384_sign(uj);
    case kCryptoLibFiSubcommandP384Verify:
      return handle_cryptolib_fi_p384_verify(uj);
    case kCryptoLibFiSubcommandSecp256k1BaseMul:
      return handle_cryptolib_fi_secp256k1_base_mul(uj);
    case kCryptoLibFiSubcommandSecp256k1PointMul:
      return handle_cryptolib_fi_secp256k1_point_mul(uj);
    case kCryptoLibFiSubcommandSecp256k1Sign:
      return handle_cryptolib_fi_secp256k1_sign(uj);
    case kCryptoLibFiSubcommandSecp256k1Verify:
      return handle_cryptolib_fi_secp256k1_verify(uj);
    case kCryptoLibFiSubcommandX25519BaseMul:
      return handle_cryptolib_fi_x25519_base_mul(uj);
    case kCryptoLibFiSubcommandX25519PointMul:
      return handle_cryptolib_fi_x25519_point_mul(uj);
    case kCryptoLibFiSubcommandEd25519BaseMul:
      return handle_cryptolib_fi_ed25519_base_mul(uj);
    case kCryptoLibFiSubcommandEd25519Sign:
      return handle_cryptolib_fi_ed25519_sign(uj);
    case kCryptoLibFiSubcommandEd25519Verify:
      return handle_cryptolib_fi_ed25519_verify(uj);
    case kCryptoLibFiSubcommandInit:
      return handle_cryptolib_fi_init(uj);
    default:
      LOG_ERROR("Unrecognized CryptoLib FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
