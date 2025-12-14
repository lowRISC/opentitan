// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/cryptolib_fi_asym.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/security_config.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/firmware/fi/cryptolib_fi_asym_impl.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_fi_asym_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define MODULE_ID MAKE_MODULE_ID('c', 'f', 'a')

// Interface to Ibex.
static dif_rv_core_ibex_t rv_core_ibex;

status_t handle_cryptolib_fi_asym_rsa_enc(ujson_t *uj) {
  cryptolib_fi_asym_rsa_enc_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_rsa_enc_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform an RSA encryption with hashing and padding options.
  // You can give cfg a value such that the RSA generates its own private key.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_rsa_enc_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status =
      (size_t)cryptolib_fi_rsa_enc_impl(uj_input, &uj_output).value;
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_fi_asym_rsa_enc_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_rsa_sign(ujson_t *uj) {
  cryptolib_fi_asym_rsa_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_rsa_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform an RSA signing with hashing and padding options.
  // You can give cfg a value such that the RSA generates its own private key.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_rsa_sign_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status =
      (size_t)cryptolib_fi_rsa_sign_impl(uj_input, &uj_output).value;
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_fi_asym_rsa_sign_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_rsa_verify(ujson_t *uj) {
  cryptolib_fi_asym_rsa_verify_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_rsa_verify_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform an RSA verification with hashing and padding options.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_rsa_verify_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status =
      (size_t)cryptolib_fi_rsa_verify_impl(uj_input, &uj_output).value;
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_fi_asym_rsa_verify_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_prime(ujson_t *uj) {
  cryptolib_fi_asym_prime_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_prime_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Generate a prime.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_prime_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memset(uj_output.prime, 0, RSA_CMD_MAX_MESSAGE_BYTES);
  uj_output.prime_len = RSA_CMD_MAX_MESSAGE_BYTES;
  uj_output.cfg = 0;
  uj_output.status = 0;

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_prime_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_p256_base_mul(ujson_t *uj) {
  cryptolib_fi_asym_p256_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_p256_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in P256.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_p256_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_p256_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_p256_point_mul(ujson_t *uj) {
  cryptolib_fi_asym_p256_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_p256_point_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in P256.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_p256_point_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_p256_point_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_p256_ecdh(ujson_t *uj) {
  cryptolib_fi_asym_p256_ecdh_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_p256_ecdh_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform ecdh in P256.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_p256_ecdh_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status =
      (size_t)cryptolib_fi_p256_ecdh_impl(uj_input, &uj_output).value;

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_fi_asym_p256_ecdh_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_p256_sign(ujson_t *uj) {
  cryptolib_fi_asym_p256_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_p256_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a P256 signature.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_p256_sign_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status =
      (size_t)cryptolib_fi_p256_sign_impl(uj_input, &uj_output).value;

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_fi_asym_p256_sign_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_p256_verify(ujson_t *uj) {
  cryptolib_fi_asym_p256_verify_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_p256_verify_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a P256 verification.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_p256_verify_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status =
      (size_t)cryptolib_fi_p256_verify_impl(uj_input, &uj_output).value;

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_fi_asym_p256_verify_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_p384_base_mul(ujson_t *uj) {
  cryptolib_fi_asym_p384_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_p384_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in p384.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_p384_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_p384_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_p384_point_mul(ujson_t *uj) {
  cryptolib_fi_asym_p384_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_p384_point_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in p384.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_p384_point_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_p384_point_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_p384_ecdh(ujson_t *uj) {
  cryptolib_fi_asym_p384_ecdh_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_p384_ecdh_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform ecdh in P384.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_p384_ecdh_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status =
      (size_t)cryptolib_fi_p384_ecdh_impl(uj_input, &uj_output).value;

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_fi_asym_p384_ecdh_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_p384_sign(ujson_t *uj) {
  cryptolib_fi_asym_p384_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_p384_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a p384 signature.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_p384_sign_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status =
      (size_t)cryptolib_fi_p384_sign_impl(uj_input, &uj_output).value;

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_fi_asym_p384_sign_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_p384_verify(ujson_t *uj) {
  cryptolib_fi_asym_p384_verify_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_p384_verify_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a p384 verification.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_p384_verify_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status =
      (size_t)cryptolib_fi_p384_verify_impl(uj_input, &uj_output).value;

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_fi_asym_p384_verify_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_secp256k1_base_mul(ujson_t *uj) {
  cryptolib_fi_asym_secp256k1_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_secp256k1_base_mul_in_t(uj,
                                                                  &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in secp256k1.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_secp256k1_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_secp256k1_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_secp256k1_point_mul(ujson_t *uj) {
  cryptolib_fi_asym_secp256k1_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_secp256k1_point_mul_in_t(uj,
                                                                   &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in secp256k1.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_secp256k1_point_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_secp256k1_point_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_secp256k1_ecdh(ujson_t *uj) {
  cryptolib_fi_asym_secp256k1_ecdh_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_secp256k1_ecdh_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform ecdh in secp256k1.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_secp256k1_ecdh_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_secp256k1_ecdh_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_secp256k1_sign(ujson_t *uj) {
  cryptolib_fi_asym_secp256k1_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_secp256k1_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a secp256k1 signature.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_secp256k1_sign_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_secp256k1_sign_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_secp256k1_verify(ujson_t *uj) {
  cryptolib_fi_asym_secp256k1_verify_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_secp256k1_verify_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a secp256k1 verification.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_secp256k1_verify_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  uj_output.result = true;
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_secp256k1_verify_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_x25519_base_mul(ujson_t *uj) {
  cryptolib_fi_asym_x25519_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_x25519_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in X25519.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_x25519_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_x25519_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_x25519_point_mul(ujson_t *uj) {
  cryptolib_fi_asym_x25519_point_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_x25519_point_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a point multiplication in X25519.
  // The Bob scalar is transformed to a public key to then be multiplied to the
  // Alice scalar. Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_x25519_point_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_x25519_point_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_x25519_ecdh(ujson_t *uj) {
  cryptolib_fi_asym_x25519_ecdh_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_x25519_ecdh_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform ecdh in x25519.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_x25519_ecdh_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_x25519_ecdh_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_ed25519_base_mul(ujson_t *uj) {
  cryptolib_fi_asym_ed25519_base_mul_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_ed25519_base_mul_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a base point multiplication in ED25519.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_ed25519_base_mul_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_ed25519_base_mul_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_ed25519_sign(ujson_t *uj) {
  cryptolib_fi_asym_ed25519_sign_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_ed25519_sign_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a ED25519 signature.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_ed25519_sign_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_ed25519_sign_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_ed25519_verify(ujson_t *uj) {
  cryptolib_fi_asym_ed25519_verify_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_asym_ed25519_verify_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a ED25519 verification.
  // Trigger are over the API calls.

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  cryptolib_fi_asym_ed25519_verify_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  uj_output.result = true;

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  /////////////// STUB END ///////////////
  RESP_OK(ujson_serialize_cryptolib_fi_asym_ed25519_verify_out_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_asym_init(ujson_t *uj) {
  // Configure the device.
  pentest_setup_device(uj, true, false);

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

status_t handle_cryptolib_fi_asym(ujson_t *uj) {
  cryptolib_fi_asym_subcommand_t cmd;
  TRY(ujson_deserialize_cryptolib_fi_asym_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kCryptoLibFiAsymSubcommandRsaEnc:
      return handle_cryptolib_fi_asym_rsa_enc(uj);
    case kCryptoLibFiAsymSubcommandRsaSign:
      return handle_cryptolib_fi_asym_rsa_sign(uj);
    case kCryptoLibFiAsymSubcommandRsaVerify:
      return handle_cryptolib_fi_asym_rsa_verify(uj);
    case kCryptoLibFiAsymSubcommandPrime:
      return handle_cryptolib_fi_asym_prime(uj);
    case kCryptoLibFiAsymSubcommandP256BaseMul:
      return handle_cryptolib_fi_asym_p256_base_mul(uj);
    case kCryptoLibFiAsymSubcommandP256PointMul:
      return handle_cryptolib_fi_asym_p256_point_mul(uj);
    case kCryptoLibFiAsymSubcommandP256Ecdh:
      return handle_cryptolib_fi_asym_p256_ecdh(uj);
    case kCryptoLibFiAsymSubcommandP256Sign:
      return handle_cryptolib_fi_asym_p256_sign(uj);
    case kCryptoLibFiAsymSubcommandP256Verify:
      return handle_cryptolib_fi_asym_p256_verify(uj);
    case kCryptoLibFiAsymSubcommandP384BaseMul:
      return handle_cryptolib_fi_asym_p384_base_mul(uj);
    case kCryptoLibFiAsymSubcommandP384PointMul:
      return handle_cryptolib_fi_asym_p384_point_mul(uj);
    case kCryptoLibFiAsymSubcommandP384Ecdh:
      return handle_cryptolib_fi_asym_p384_ecdh(uj);
    case kCryptoLibFiAsymSubcommandP384Sign:
      return handle_cryptolib_fi_asym_p384_sign(uj);
    case kCryptoLibFiAsymSubcommandP384Verify:
      return handle_cryptolib_fi_asym_p384_verify(uj);
    case kCryptoLibFiAsymSubcommandSecp256k1BaseMul:
      return handle_cryptolib_fi_asym_secp256k1_base_mul(uj);
    case kCryptoLibFiAsymSubcommandSecp256k1PointMul:
      return handle_cryptolib_fi_asym_secp256k1_point_mul(uj);
    case kCryptoLibFiAsymSubcommandSecp256k1Ecdh:
      return handle_cryptolib_fi_asym_secp256k1_ecdh(uj);
    case kCryptoLibFiAsymSubcommandSecp256k1Sign:
      return handle_cryptolib_fi_asym_secp256k1_sign(uj);
    case kCryptoLibFiAsymSubcommandSecp256k1Verify:
      return handle_cryptolib_fi_asym_secp256k1_verify(uj);
    case kCryptoLibFiAsymSubcommandX25519BaseMul:
      return handle_cryptolib_fi_asym_x25519_base_mul(uj);
    case kCryptoLibFiAsymSubcommandX25519PointMul:
      return handle_cryptolib_fi_asym_x25519_point_mul(uj);
    case kCryptoLibFiAsymSubcommandX25519Ecdh:
      return handle_cryptolib_fi_asym_x25519_ecdh(uj);
    case kCryptoLibFiAsymSubcommandEd25519BaseMul:
      return handle_cryptolib_fi_asym_ed25519_base_mul(uj);
    case kCryptoLibFiAsymSubcommandEd25519Sign:
      return handle_cryptolib_fi_asym_ed25519_sign(uj);
    case kCryptoLibFiAsymSubcommandEd25519Verify:
      return handle_cryptolib_fi_asym_ed25519_verify(uj);
    case kCryptoLibFiAsymSubcommandInit:
      return handle_cryptolib_fi_asym_init(uj);
    default:
      LOG_ERROR("Unrecognized CryptoLib FI ASYM subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
