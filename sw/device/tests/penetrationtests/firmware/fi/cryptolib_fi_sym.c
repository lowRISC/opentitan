// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/cryptolib_fi_sym.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/security_config.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/firmware/fi/cryptolib_fi_sym_impl.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_fi_sym_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

status_t handle_cryptolib_fi_sym_aes(ujson_t *uj) {
  cryptolib_fi_sym_aes_in_t uj_input;
  TRY(ujson_deserialize_cryptolib_fi_sym_aes_in_t(uj, &uj_input));

  /////////////// STUB START ///////////////
  // Perform an AES encryption or decryption.
  // Adjust the mode of operation and the padding mode.
  // The total size of this test can be large due to all these options.
  // Triggers are over the API calls.
  cryptolib_fi_sym_aes_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status = (size_t)cryptolib_fi_aes_impl(uj_input, &uj_output).value;
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

  cryptolib_fi_sym_cmac_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
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
  cryptolib_fi_sym_gcm_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status = (size_t)cryptolib_fi_gcm_impl(uj_input, &uj_output).value;
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

  cryptolib_fi_sym_tdes_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
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
  cryptolib_fi_sym_hmac_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status = (size_t)cryptolib_fi_hmac_impl(uj_input, &uj_output).value;
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
  cryptolib_fi_sym_drbg_generate_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status =
      (size_t)cryptolib_fi_drbg_generate_impl(uj_input, &uj_output).value;
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
  cryptolib_fi_sym_drbg_reseed_out_t uj_output;
  uj_output.status = kUnknown;
  uj_output.status =
      (size_t)cryptolib_fi_drbg_reseed_impl(uj_input, &uj_output).value;
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
  cryptolib_fi_sym_trng_generate_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
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
  cryptolib_fi_sym_trng_init_out_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  /////////////// STUB END ///////////////

  RESP_OK(ujson_serialize_cryptolib_fi_sym_trng_init_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_cryptolib_fi_sym_init(ujson_t *uj) {
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
      uj_alert_data.enable_loc_alerts, uj_alert_data.enable_classes,
      uj_alert_data.accumulation_thresholds, uj_alert_data.signals,
      uj_alert_data.duration_cycles, uj_alert_data.ping_timeout);

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
