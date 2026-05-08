// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/cryptolib_fi_sym.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/security_config.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/firmware/fi/cryptolib_fi_sym_impl.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_fi_sym_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Interface to Ibex.
static dif_rv_core_ibex_t rv_core_ibex;

status_t handle_cryptolib_fi_sym_aes(ujson_t *uj) {
  cryptolib_fi_sym_aes_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_sym_aes_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform an AES encryption or decryption.
  // Adjust the mode of operation and the padding mode.
  // The total size of this test can be large due to all these options.
  // Triggers are over the API calls.

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

  cryptolib_fi_sym_aes_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status = (size_t)cryptolib_fi_aes_impl(uj_input, &uj_output).value;

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

  RESP_OK(ujson_serialize_cryptolib_fi_sym_aes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_sym_cmac(ujson_t *uj) {
  cryptolib_fi_sym_cmac_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_sym_cmac_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a CMAC encryption.
  // Verify the tag before sending the output.
  // Triggers are over the API calls.

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

  cryptolib_fi_sym_cmac_out_t uj_output;
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
  RESP_OK(ujson_serialize_cryptolib_fi_sym_cmac_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_sym_gcm(ujson_t *uj) {
  cryptolib_fi_sym_gcm_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_sym_gcm_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a GCM encryption with aad and generate a tag.
  // Then, verify that tag again, before sending the output.
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

  cryptolib_fi_sym_gcm_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status = (size_t)cryptolib_fi_gcm_impl(uj_input, &uj_output).value;

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

  RESP_OK(ujson_serialize_cryptolib_fi_sym_gcm_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_sym_tdes(ujson_t *uj) {
  cryptolib_fi_sym_tdes_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_sym_tdes_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a TDES encryption or decryption.
  // Adjust the mode of operation and the padding mode.
  // Triggers are over the API calls.

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

  cryptolib_fi_sym_tdes_out_t uj_output;
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
  RESP_OK(ujson_serialize_cryptolib_fi_sym_tdes_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_cryptolib_fi_sym_hmac(ujson_t *uj) {
  cryptolib_fi_sym_hmac_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_sym_hmac_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform an HMAC call.
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

  cryptolib_fi_sym_hmac_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status = (size_t)cryptolib_fi_hmac_impl(uj_input, &uj_output).value;

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

  RESP_OK(ujson_serialize_cryptolib_fi_sym_hmac_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_sym_drbg_generate(ujson_t *uj) {
  cryptolib_fi_sym_drbg_generate_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_sym_drbg_generate_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a DRBG call to generate random output.
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

  cryptolib_fi_sym_drbg_generate_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status =
      (size_t)cryptolib_fi_drbg_generate_impl(uj_input, &uj_output).value;

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

  RESP_OK(ujson_serialize_cryptolib_fi_sym_drbg_generate_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_sym_drbg_reseed(ujson_t *uj) {
  cryptolib_fi_sym_drbg_reseed_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_sym_drbg_reseed_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a DRBG call to reseed/instantiate the DRBG.
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

  cryptolib_fi_sym_drbg_reseed_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status =
      (size_t)cryptolib_fi_drbg_reseed_impl(uj_input, &uj_output).value;

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

  RESP_OK(ujson_serialize_cryptolib_fi_sym_drbg_reseed_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_sym_trng_generate(ujson_t *uj) {
  cryptolib_fi_sym_trng_generate_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_sym_trng_generate_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a TRNG call to generate random output.
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

  cryptolib_fi_sym_trng_generate_out_t uj_output;
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

  RESP_OK(ujson_serialize_cryptolib_fi_sym_trng_generate_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_sym_trng_init(ujson_t *uj) {
  cryptolib_fi_sym_trng_init_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_sym_trng_init_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform a TRNG call to instantiate the TRNG.
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

  cryptolib_fi_sym_trng_init_out_t uj_output;
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

  RESP_OK(ujson_serialize_cryptolib_fi_sym_trng_init_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_sym_init(ujson_t *uj) {
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

status_t handle_cryptolib_fi_sym(ujson_t *uj) {
  cryptolib_fi_sym_subcommand_t cmd;
  TRY(ujson_deserialize_cryptolib_fi_sym_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kCryptoLibFiSymSubcommandAes:
      return handle_cryptolib_fi_sym_aes(uj);
    case kCryptoLibFiSymSubcommandCmac:
      return handle_cryptolib_fi_sym_cmac(uj);
    case kCryptoLibFiSymSubcommandGcm:
      return handle_cryptolib_fi_sym_gcm(uj);
    case kCryptoLibFiSymSubcommandTdes:
      return handle_cryptolib_fi_sym_tdes(uj);
    case kCryptoLibFiSymSubcommandHmac:
      return handle_cryptolib_fi_sym_hmac(uj);
    case kCryptoLibFiSymSubcommandDrbgGenerate:
      return handle_cryptolib_fi_sym_drbg_generate(uj);
    case kCryptoLibFiSymSubcommandDrbgReseed:
      return handle_cryptolib_fi_sym_drbg_reseed(uj);
    case kCryptoLibFiSymSubcommandTrngGenerate:
      return handle_cryptolib_fi_sym_trng_generate(uj);
    case kCryptoLibFiSymSubcommandTrngInit:
      return handle_cryptolib_fi_sym_trng_init(uj);
    case kCryptoLibFiSymSubcommandInit:
      return handle_cryptolib_fi_sym_init(uj);
    default:
      LOG_ERROR("Unrecognized CryptoLib FI SYM subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
