// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/crypto_fi.h"

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/crypto_fi_commands.h"

#include "aes_regs.h"
#include "hmac_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"

#define SHADOW_REG_ACCESS(shadow_reg_addr, tmp)    \
  abs_mmio_write32_shadowed(shadow_reg_addr, tmp); \
  tmp = abs_mmio_read32(shadow_reg_addr);

#define SHADOW_REG_ACCESS_10(shadow_reg_addr, tmp) \
  SHADOW_REG_ACCESS(shadow_reg_addr, tmp)          \
  SHADOW_REG_ACCESS(shadow_reg_addr, tmp)          \
  SHADOW_REG_ACCESS(shadow_reg_addr, tmp)          \
  SHADOW_REG_ACCESS(shadow_reg_addr, tmp)          \
  SHADOW_REG_ACCESS(shadow_reg_addr, tmp)          \
  SHADOW_REG_ACCESS(shadow_reg_addr, tmp)          \
  SHADOW_REG_ACCESS(shadow_reg_addr, tmp)          \
  SHADOW_REG_ACCESS(shadow_reg_addr, tmp)          \
  SHADOW_REG_ACCESS(shadow_reg_addr, tmp)          \
  SHADOW_REG_ACCESS(shadow_reg_addr, tmp)

enum {
  /**
   * Timeout for waiting that an AES operation has completed.
   */
  kAesWaitTimeout = 1000000,
};

static dif_aes_t aes;
static dif_kmac_t kmac;
static dif_hmac_t hmac;
// Interface to Ibex.
static dif_rv_core_ibex_t rv_core_ibex;

/**
 * KMAC test description.
 */
typedef struct kmac_test {
  dif_kmac_mode_kmac_t mode;
  dif_kmac_key_t key;

  const char *message;
  size_t message_len;

  const char *customization_string;
  size_t customization_string_len;

  const uint32_t digest[16];
  size_t digest_len;
  bool digest_len_is_fixed;
} kmac_test_t;

/**
 * A single KMAC example:
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/KMAC_samples.pdf
 */
static const kmac_test_t kKmacTestVector = {
    .mode = kDifKmacModeKmacLen256,
    .key =
        (dif_kmac_key_t){
            .share0 = {0x43424140, 0x47464544, 0x4b4a4948, 0x4f4e4f4c,
                       0x53525150, 0x57565554, 0x5b5a5958, 0x5f5e5d5c},
            .share1 = {0},
            .length = kDifKmacKeyLen256,
        },
    .message =
        "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f"
        "\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"
        "\x20\x21\x22\x23\x24\x25\x26\x27\x28\x29\x2a\x2b\x2c\x2d\x2e\x2f"
        "\x30\x31\x32\x33\x34\x35\x36\x37\x38\x39\x3a\x3b\x3c\x3d\x3e\x3f"
        "\x40\x41\x42\x43\x44\x45\x46\x47\x48\x49\x4a\x4b\x4c\x4d\x4e\x4f"
        "\x50\x51\x52\x53\x54\x55\x56\x57\x58\x59\x5a\x5b\x5c\x5d\x5e\x5f"
        "\x60\x61\x62\x63\x64\x65\x66\x67\x68\x69\x6a\x6b\x6c\x6d\x6e\x6f"
        "\x70\x71\x72\x73\x74\x75\x76\x77\x78\x79\x7a\x7b\x7c\x7d\x7e\x7f"
        "\x80\x81\x82\x83\x84\x85\x86\x87\x88\x89\x8a\x8b\x8c\x8d\x8e\x8f"
        "\x90\x91\x92\x93\x94\x95\x96\x97\x98\x99\x9a\x9b\x9c\x9d\x9e\x9f"
        "\xa0\xa1\xa2\xa3\xa4\xa5\xa6\xa7\xa8\xa9\xaa\xab\xac\xad\xae\xaf"
        "\xb0\xb1\xb2\xb3\xb4\xb5\xb6\xb7\xb8\xb9\xba\xbb\xbc\xbd\xbe\xbf"
        "\xc0\xc1\xc2\xc3\xc4\xc5\xc6\xc7",
    .message_len = 200,
    .customization_string = "My Tagged Application",
    .customization_string_len = 21,
    .digest = {0x1c73bed5, 0x73d74e95, 0x59bb4628, 0xe3a8e3db, 0x7ae7830f,
               0x5944ff4b, 0xb4c2f1f2, 0xceb8ebec, 0xc601ba67, 0x57b88a2e,
               0x9b492d8d, 0x6727bbd1, 0x90117868, 0x6a300a02, 0x1d28de97,
               0x5d3030cc},
    .digest_len = 16,
    .digest_len_is_fixed = false,
};

static dif_aes_transaction_t transaction = {
    .operation = kDifAesOperationEncrypt,
    .mode = kDifAesModeEcb,
    .key_len = kDifAesKey128,
    .manual_operation = kDifAesManualOperationManual,
    .key_provider = kDifAesKeySoftwareProvided,
    .mask_reseeding = kDifAesReseedPer8kBlock,
    .reseed_on_key_change = false,
    .force_masks = false,
    .ctrl_aux_lock = false,
};

/**
 * Spins until the AES hardware reports a specific status bit.
 */
static inline uint32_t aes_spin_until(uint32_t bit) {
  while (true) {
    uint32_t reg =
        abs_mmio_read32(TOP_EARLGREY_AES_BASE_ADDR + AES_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, AES_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT) ||
        bitfield_bit32_read(reg, AES_STATUS_ALERT_FATAL_FAULT_BIT)) {
      return 1;
    }
    if (bitfield_bit32_read(reg, bit)) {
      return 0;
    }
  }
}

status_t handle_crypto_fi_aes(ujson_t *uj) {
  // Get the plaintext and key.
  crypto_fi_aes_input_t uj_input;
  TRY(ujson_deserialize_crypto_fi_aes_input_t(uj, &uj_input));
  // Get the test mode.
  crypto_fi_aes_mode_t uj_data;
  TRY(ujson_deserialize_crypto_fi_aes_mode_t(uj, &uj_data));

  // Copy in the plaintext and key
  dif_aes_data_t aes_plaintext;
  memcpy(aes_plaintext.data, uj_input.plaintext, sizeof(aes_plaintext.data));
  dif_aes_key_share_t aes_key_shares;
  // Mask the provided key.
  for (int i = 0; i < 4; ++i) {
    aes_key_shares.share1[i] = pentest_non_linear_layer(
        pentest_linear_layer(pentest_next_lfsr(1, kPentestLfsrMasking)));
    aes_key_shares.share0[i] =
        *((uint32_t *)uj_input.key + i) ^ aes_key_shares.share1[i];
  }
  // Provide random shares for unused key bits.
  for (size_t i = 4; i < 8; ++i) {
    aes_key_shares.share1[i] =
        pentest_non_linear_layer(pentest_next_lfsr(1, kPentestLfsrMasking));
    aes_key_shares.share0[i] =
        pentest_non_linear_layer(pentest_next_lfsr(1, kPentestLfsrMasking));
  }

  // Reset the AES
  TRY(dif_aes_reset(&aes));

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Write the key into the AES block. Set and unset the trigger when
  // key_trigger is true.
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kAesWaitTimeout);
  if (uj_data.key_trigger) {
    pentest_set_trigger_high();
  }
  TRY(dif_aes_start(&aes, &transaction, &aes_key_shares, NULL));
  // Busy polling because AES_TESTUTILS_WAIT_FOR_STATUS seems to take longer
  // (~100us) as expected.
  while (!aes_testutils_get_status(&aes, kDifAesStatusInputReady))
    ;
  if (uj_data.key_trigger) {
    pentest_set_trigger_low();
  }

  // Write the plaintext into the AES block. Set and unset the trigger when
  // plaintext_trigger is true.
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kAesWaitTimeout);
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                                kAesWaitTimeout);
  if (uj_data.plaintext_trigger) {
    pentest_set_trigger_high();
  }
  TRY(dif_aes_load_data(&aes, aes_plaintext));
  if (uj_data.plaintext_trigger) {
    pentest_set_trigger_low();
  }

  // Start the encryption. Set and unset the trigger when encrypt_trigger is
  // true.
  if (uj_data.encrypt_trigger) {
    pentest_set_trigger_high();
  }
  asm volatile(NOP30);
  TRY(dif_aes_trigger(&aes, kDifAesTriggerStart));
  // Busy polling because AES_TESTUTILS_WAIT_FOR_STATUS seems to take longer
  // (~100us) as expected.
  while (!aes_testutils_get_status(&aes, kDifAesStatusOutputValid))
    ;
  asm volatile(NOP30);
  if (uj_data.encrypt_trigger) {
    pentest_set_trigger_low();
  }

  // Read the ciphertext. Set and unset the trigger when ciphertext_trigger is
  // true.
  dif_aes_data_t ciphertext;
  if (uj_data.ciphertext_trigger) {
    pentest_set_trigger_high();
  }
  TRY(dif_aes_read_output(&aes, &ciphertext));
  if (uj_data.ciphertext_trigger) {
    pentest_set_trigger_low();
  }

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send the ciphertext and the alerts back to the host.
  crypto_fi_aes_ciphertext_t uj_output;
  uj_output.err_status = codes;
  memcpy(uj_output.ciphertext, ciphertext.data, 16);
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_crypto_fi_aes_ciphertext_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_crypto_fi_init(ujson_t *uj) {
  penetrationtest_cpuctrl_t uj_cpuctrl_data;
  TRY(ujson_deserialize_penetrationtest_cpuctrl_t(uj, &uj_cpuctrl_data));
  penetrationtest_sensor_config_t uj_sensor_data;
  TRY(ujson_deserialize_penetrationtest_sensor_config_t(uj, &uj_sensor_data));
  penetrationtest_alert_config_t uj_alert_data;
  TRY(ujson_deserialize_penetrationtest_alert_config_t(uj, &uj_alert_data));

  pentest_select_trigger_type(kPentestTriggerTypeSw);
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralAes |
                   kPentestPeripheralKmac | kPentestPeripheralEdn |
                   kPentestPeripheralCsrng | kPentestPeripheralEntropy |
                   kPentestPeripheralHmac,
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

  // Init the AES block.
  TRY(dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));

  // Init the KMAC block.
  TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .entropy_fast_process = kDifToggleDisabled,
      .entropy_seed = {0xaa25b4bf, 0x48ce8fff, 0x5a78282a, 0x48465647,
                       0x70410fef},
      .message_big_endian = kDifToggleDisabled,
      .output_big_endian = kDifToggleDisabled,
      .sideload = kDifToggleDisabled,
      .msg_mask = kDifToggleEnabled,
  };

  TRY(dif_kmac_configure(&kmac, config));

  // Init the HMAC block.
  mmio_region_t base_addr = mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR);
  TRY(dif_hmac_init(base_addr, &hmac));

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

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

  return OK_STATUS();
}

status_t handle_crypto_fi_kmac(ujson_t *uj) {
  // Get the test mode.
  crypto_fi_kmac_mode_t uj_data;
  TRY(ujson_deserialize_crypto_fi_kmac_mode_t(uj, &uj_data));
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Configure and write key to the KMAC block. Set and unset the trigger when
  // key_trigger is true.
  dif_kmac_operation_state_t kmac_operation_state;
  if (uj_data.key_trigger) {
    pentest_set_trigger_high();
  }

  TRY(dif_kmac_mode_kmac_start(&kmac, &kmac_operation_state,
                               kKmacTestVector.mode, 0, &kKmacTestVector.key,
                               NULL));
  if (uj_data.key_trigger) {
    pentest_set_trigger_low();
  }

  // Absorb. Set and unset the trigger when absorb_trigger is true.
  if (uj_data.absorb_trigger) {
    pentest_set_trigger_high();
  }
  TRY(dif_kmac_absorb(&kmac, &kmac_operation_state, kKmacTestVector.message,
                      kKmacTestVector.message_len, NULL));
  if (uj_data.absorb_trigger) {
    pentest_set_trigger_low();
  }

  // Static. Set and unset the trigger when static_trigger is true.
  if (uj_data.static_trigger) {
    pentest_set_trigger_high();
  }
  asm volatile(NOP30);
  asm volatile(NOP30);
  asm volatile(NOP30);
  if (uj_data.static_trigger) {
    pentest_set_trigger_low();
  }

  // Squeeze. Set and unset the trigger when squeeze_trigger is true.
  uint32_t digest[kKmacTestVector.digest_len];
  if (uj_data.squeeze_trigger) {
    pentest_set_trigger_high();
  }
  TRY(dif_kmac_squeeze(&kmac, &kmac_operation_state, digest,
                       kKmacTestVector.digest_len, /*processed=*/NULL,
                       /*capacity=*/NULL));
  if (uj_data.squeeze_trigger) {
    pentest_set_trigger_low();
  }

  // 2nd Squeeze. This shall enforce a permutation. Any injected fault will
  // result in a completely different digest. Hence, allows for easy detection
  // of an injected fault.
  uint32_t digest_2nd[kKmacTestVector.digest_len];
  TRY(dif_kmac_squeeze(&kmac, &kmac_operation_state, digest_2nd,
                       kKmacTestVector.digest_len, /*processed=*/NULL,
                       /*capacity=*/NULL));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  TRY(dif_kmac_end(&kmac, &kmac_operation_state));

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send the first 8 bytes of the digest and the alerts back to the host.
  crypto_fi_kmac_digest_t uj_output;
  uj_output.err_status = codes;
  memcpy(uj_output.digest, (uint8_t *)digest, 8);
  memcpy(uj_output.digest_2nd, (uint8_t *)digest_2nd, 8);
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_crypto_fi_kmac_digest_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_crypto_fi_kmac_state(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Configure and write key to the KMAC block.
  dif_kmac_operation_state_t kmac_operation_state;
  TRY(dif_kmac_mode_kmac_start(&kmac, &kmac_operation_state,
                               kKmacTestVector.mode, 0, &kKmacTestVector.key,
                               NULL));
  // Absorb.
  TRY(dif_kmac_absorb(&kmac, &kmac_operation_state, kKmacTestVector.message,
                      kKmacTestVector.message_len, NULL));

  // Squeeze. Set and unset the trigger when squeeze_trigger is true.
  uint32_t digest[kKmacTestVector.digest_len];
  TRY(dif_kmac_squeeze(&kmac, &kmac_operation_state, digest,
                       kKmacTestVector.digest_len, /*processed=*/NULL,
                       /*capacity=*/NULL));

  // Static.
  pentest_set_trigger_high();
  asm volatile(NOP30);
  asm volatile(NOP30);
  asm volatile(NOP30);
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send the Keccak state and the alerts back to the host.
  crypto_fi_kmac_state_t uj_output;
  // Read Keccak state shares
  const mmio_region_t base = kmac.base_addr;
  ptrdiff_t offset = KMAC_STATE_REG_OFFSET;
  for (size_t i = 0; i < 200; i++) {
    uj_output.share0[i] = mmio_region_read8(base, offset);
    uj_output.share1[i] =
        mmio_region_read8(base, offset + kDifKmacStateShareOffset);
    offset += sizeof(uint8_t);
  }
  // Read error, digest, and alerts
  uj_output.err_status = codes;
  memcpy(uj_output.digest, (uint8_t *)digest, 8);
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));

  RESP_OK(ujson_serialize_crypto_fi_kmac_state_t, uj, &uj_output);

  TRY(dif_kmac_end(&kmac, &kmac_operation_state));
  return OK_STATUS();
}

status_t handle_crypto_fi_hmac(ujson_t *uj) {
  // Get the message and key.
  crypto_fi_hmac_input_t uj_input;
  TRY(ujson_deserialize_crypto_fi_hmac_input_t(uj, &uj_input));
  // Get the test mode.
  crypto_fi_hmac_mode_t uj_data;
  TRY(ujson_deserialize_crypto_fi_hmac_mode_t(uj, &uj_data));
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();

  // hash_mode 0 equals SHA256, 1 equals SHA384, and 2 equals SHA512
  uint32_t digest_cfg_size = 0;
  uint32_t key_cfg_size = 0;
  uint32_t digest_word_size = 0;
  uint32_t key_word_size = 0;
  switch (uj_data.hash_mode) {
    case 0:
      digest_cfg_size = HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_256;
      key_cfg_size = HMAC_CFG_KEY_LENGTH_VALUE_KEY_256;
      digest_word_size = 8;
      key_word_size = 8;
      break;
    case 1:
      digest_cfg_size = HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_384;
      key_cfg_size = HMAC_CFG_KEY_LENGTH_VALUE_KEY_384;
      digest_word_size = 12;
      key_word_size = 12;
      break;
    case 2:
      digest_cfg_size = HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_512;
      key_cfg_size = HMAC_CFG_KEY_LENGTH_VALUE_KEY_512;
      digest_word_size = 16;
      key_word_size = 16;
      break;
    default:
      digest_cfg_size = HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_256;
      key_cfg_size = HMAC_CFG_KEY_LENGTH_VALUE_KEY_256;
      digest_word_size = 8;
      key_word_size = 8;
  }

  if (uj_data.start_trigger) {
    pentest_set_trigger_high();
  }
  // This mimics dif_hmac_mode_sha256_start, however, we need to include SHA384
  // and SHA512 as well.
  uint32_t reg = mmio_region_read32(hmac.base_addr, HMAC_CFG_REG_OFFSET);

  // Set the byte-order of the input message and the digest.
  reg = bitfield_bit32_write(reg, HMAC_CFG_ENDIAN_SWAP_BIT,
                             uj_data.message_endianness_big);
  reg = bitfield_bit32_write(reg, HMAC_CFG_DIGEST_SWAP_BIT,
                             uj_data.digest_endianness_big);
  reg = bitfield_bit32_write(reg, HMAC_CFG_KEY_SWAP_BIT,
                             uj_data.key_endianness_big);

  // Set HMAC to process in SHA2 or HMAC mode.
  reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, uj_data.enable_hmac);

  // Set digest size.
  reg =
      bitfield_field32_write(reg, HMAC_CFG_DIGEST_SIZE_FIELD, digest_cfg_size);
  // Set key size.
  reg = bitfield_field32_write(reg, HMAC_CFG_KEY_LENGTH_FIELD, key_cfg_size);
  // Set the key size (only matters for HMAC).
  reg = bitfield_field32_write(reg, HMAC_CFG_KEY_LENGTH_FIELD, key_cfg_size);

  // Write new CFG register value.
  mmio_region_write32(hmac.base_addr, HMAC_CFG_REG_OFFSET, reg);

  // Write the key.
  if (uj_data.enable_hmac) {
    for (size_t i = 0; i < key_word_size; ++i) {
      abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_KEY_0_REG_OFFSET +
                           i * sizeof(uint32_t),
                       uj_input.key[i]);
    }
  }

  // Begin HMAC operation.
  mmio_region_nonatomic_set_bit32(hmac.base_addr, HMAC_CMD_REG_OFFSET,
                                  HMAC_CMD_HASH_START_BIT);

  if (uj_data.start_trigger) {
    pentest_set_trigger_low();
  }

  if (uj_data.msg_trigger) {
    pentest_set_trigger_high();
  }
  TRY(hmac_testutils_push_message(&hmac, (char *)uj_input.message,
                                  sizeof(uj_input.message)));
  if (uj_data.msg_trigger) {
    pentest_set_trigger_low();
  }

  if (uj_data.process_trigger) {
    pentest_set_trigger_high();
  }
  TRY(dif_hmac_process(&hmac));
  if (uj_data.process_trigger) {
    pentest_set_trigger_low();
  }

  uint32_t digest[CRYPTOFI_HMAC_CMD_MAX_TAG_WORDS];
  memset(digest, 0, CRYPTOFI_HMAC_CMD_MAX_TAG_WORDS);
  if (uj_data.finish_trigger) {
    pentest_set_trigger_high();
  }
  // We again adapt the dif to allow for SHA384 and SHA512 outputs
  uint32_t usec;
  compute_hmac_testutils_finish_timeout_usec(&usec);
  mmio_region_nonatomic_set_bit32(hmac.base_addr, HMAC_INTR_STATE_REG_OFFSET,
                                  HMAC_INTR_STATE_HMAC_DONE_BIT);

  // Read digest
  for (size_t i = 0; i < digest_word_size; ++i) {
    digest[digest_word_size - i - 1] = mmio_region_read32(
        hmac.base_addr,
        HMAC_DIGEST_0_REG_OFFSET + (ptrdiff_t)(i * sizeof(uint32_t)));
  }

  // Disable after done
  uint32_t device_config =
      mmio_region_read32(hmac.base_addr, HMAC_CFG_REG_OFFSET);
  device_config =
      bitfield_bit32_write(device_config, HMAC_CFG_SHA_EN_BIT, false);
  device_config =
      bitfield_bit32_write(device_config, HMAC_CFG_HMAC_EN_BIT, false);
  device_config =
      bitfield_field32_write(device_config, HMAC_CFG_DIGEST_SIZE_FIELD,
                             HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_NONE);
  device_config =
      bitfield_field32_write(device_config, HMAC_CFG_KEY_LENGTH_FIELD,
                             HMAC_CFG_KEY_LENGTH_VALUE_KEY_256);

  mmio_region_write32(hmac.base_addr, HMAC_CFG_REG_OFFSET, device_config);
  if (uj_data.finish_trigger) {
    pentest_set_trigger_low();
  }

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send the digest and the alerts back to the host.
  crypto_fi_hmac_tag_t uj_output;
  uj_output.err_status = codes;
  memset(uj_output.tag, 0, sizeof(uj_output.tag));
  memcpy(uj_output.tag, digest, digest_word_size * 4);
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_crypto_fi_hmac_tag_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_crypto_fi_shadow_reg_access(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  crypto_fi_test_result_mult_t uj_output;

  // Values we want to write into the KMAC shadow registers during FI.
  uint32_t ctrl_reg_kmac = KMAC_CFG_SHADOWED_REG_RESVAL;
  ctrl_reg_kmac = bitfield_bit32_write(ctrl_reg_kmac,
                                       KMAC_CFG_SHADOWED_MSG_ENDIANNESS_BIT, 1);
  ctrl_reg_kmac = bitfield_bit32_write(
      ctrl_reg_kmac, KMAC_CFG_SHADOWED_STATE_ENDIANNESS_BIT, 1);
  ctrl_reg_kmac =
      bitfield_bit32_write(ctrl_reg_kmac, KMAC_CFG_SHADOWED_SIDELOAD_BIT, 1);
  ctrl_reg_kmac = bitfield_bit32_write(
      ctrl_reg_kmac, KMAC_CFG_SHADOWED_ENTROPY_FAST_PROCESS_BIT, 0);
  ctrl_reg_kmac =
      bitfield_bit32_write(ctrl_reg_kmac, KMAC_CFG_SHADOWED_MSG_MASK_BIT, 1);
  ctrl_reg_kmac = bitfield_bit32_write(ctrl_reg_kmac,
                                       KMAC_CFG_SHADOWED_ENTROPY_READY_BIT, 0);
  ctrl_reg_kmac = bitfield_bit32_write(
      ctrl_reg_kmac, KMAC_CFG_SHADOWED_EN_UNSUPPORTED_MODESTRENGTH_BIT, 1);

  uint32_t ctrl_reg_kmac_addr =
      TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_CFG_SHADOWED_REG_OFFSET;

  pentest_set_trigger_high();
  asm volatile(NOP10);
  SHADOW_REG_ACCESS_10(ctrl_reg_kmac_addr, ctrl_reg_kmac)
  SHADOW_REG_ACCESS_10(ctrl_reg_kmac_addr, ctrl_reg_kmac)
  SHADOW_REG_ACCESS_10(ctrl_reg_kmac_addr, ctrl_reg_kmac)
  asm volatile(NOP10);
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Read back KMAC shadow registers.
  uint32_t ctrl_reg_kmac_read = abs_mmio_read32(TOP_EARLGREY_KMAC_BASE_ADDR +
                                                KMAC_CFG_SHADOWED_REG_OFFSET);
  uj_output.result[0] = ctrl_reg_kmac_read;
  // Zeroize unused
  uj_output.result[1] = 0;
  uj_output.result[2] = 0;

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_crypto_fi_test_result_mult_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_crypto_fi_shadow_reg_read(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  crypto_fi_test_result_mult_t uj_output;

  // Initialize AES and KMAC with the default values.
  uint32_t ctrl_reg_aes_init = AES_CTRL_SHADOWED_REG_RESVAL;
  ctrl_reg_aes_init =
      bitfield_field32_write(ctrl_reg_aes_init, AES_CTRL_SHADOWED_KEY_LEN_FIELD,
                             AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128);
  ctrl_reg_aes_init =
      bitfield_field32_write(ctrl_reg_aes_init, AES_CTRL_SHADOWED_MODE_FIELD,
                             AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB);
  ctrl_reg_aes_init = bitfield_field32_write(
      ctrl_reg_aes_init, AES_CTRL_SHADOWED_PRNG_RESEED_RATE_FIELD,
      AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_64);
  ctrl_reg_aes_init = bitfield_bit32_write(
      ctrl_reg_aes_init, AES_CTRL_SHADOWED_SIDELOAD_BIT, true);
  ctrl_reg_aes_init = bitfield_field32_write(
      ctrl_reg_aes_init, AES_CTRL_SHADOWED_OPERATION_FIELD,
      AES_CTRL_SHADOWED_OPERATION_VALUE_AES_DEC);
  ctrl_reg_aes_init = bitfield_bit32_write(
      ctrl_reg_aes_init, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, true);
  abs_mmio_write32_shadowed(
      TOP_EARLGREY_AES_BASE_ADDR + AES_CTRL_SHADOWED_REG_OFFSET,
      ctrl_reg_aes_init);
  aes_spin_until(AES_STATUS_IDLE_BIT);

  uint32_t ctrl_reg_kmac_init = KMAC_CFG_SHADOWED_REG_RESVAL;
  ctrl_reg_kmac_init = bitfield_bit32_write(
      ctrl_reg_kmac_init, KMAC_CFG_SHADOWED_MSG_ENDIANNESS_BIT, 0);
  ctrl_reg_kmac_init = bitfield_bit32_write(
      ctrl_reg_kmac_init, KMAC_CFG_SHADOWED_STATE_ENDIANNESS_BIT, 0);
  ctrl_reg_kmac_init = bitfield_bit32_write(ctrl_reg_kmac_init,
                                            KMAC_CFG_SHADOWED_SIDELOAD_BIT, 0);
  ctrl_reg_kmac_init = bitfield_bit32_write(
      ctrl_reg_kmac_init, KMAC_CFG_SHADOWED_ENTROPY_FAST_PROCESS_BIT, 1);
  ctrl_reg_kmac_init = bitfield_bit32_write(ctrl_reg_kmac_init,
                                            KMAC_CFG_SHADOWED_MSG_MASK_BIT, 0);
  ctrl_reg_kmac_init = bitfield_bit32_write(
      ctrl_reg_kmac_init, KMAC_CFG_SHADOWED_ENTROPY_READY_BIT, 1);
  ctrl_reg_kmac_init = bitfield_bit32_write(
      ctrl_reg_kmac_init, KMAC_CFG_SHADOWED_EN_UNSUPPORTED_MODESTRENGTH_BIT, 0);
  abs_mmio_write32_shadowed(
      TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_CFG_SHADOWED_REG_OFFSET,
      ctrl_reg_kmac_init);

  pentest_set_trigger_high();
  asm volatile(NOP30);
  uint32_t ctrl_reg_aes_read = abs_mmio_read32(TOP_EARLGREY_AES_BASE_ADDR +
                                               AES_CTRL_SHADOWED_REG_OFFSET);
  uint32_t ctrl_reg_kmac_read = abs_mmio_read32(TOP_EARLGREY_KMAC_BASE_ADDR +
                                                KMAC_CFG_SHADOWED_REG_OFFSET);
  asm volatile(NOP30);
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Compare AES and KMAC values.
  uj_output.result[0] = 0;
  if (ctrl_reg_aes_read != ctrl_reg_aes_init) {
    uj_output.result[0] = ctrl_reg_aes_read;
  }

  uj_output.result[1] = 0;
  if (ctrl_reg_kmac_read != ctrl_reg_kmac_init) {
    uj_output.result[1] = ctrl_reg_kmac_read;
  }

  uj_output.result[2] = 0;

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_crypto_fi_test_result_mult_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_crypto_fi(ujson_t *uj) {
  crypto_fi_subcommand_t cmd;
  TRY(ujson_deserialize_crypto_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kCryptoFiSubcommandAes:
      return handle_crypto_fi_aes(uj);
    case kCryptoFiSubcommandInit:
      return handle_crypto_fi_init(uj);
    case kCryptoFiSubcommandKmac:
      return handle_crypto_fi_kmac(uj);
    case kCryptoFiSubcommandKmacState:
      return handle_crypto_fi_kmac_state(uj);
    case kCryptoFiSubcommandHmac:
      return handle_crypto_fi_hmac(uj);
    case kCryptoFiSubcommandShadowRegAccess:
      return handle_crypto_fi_shadow_reg_access(uj);
    case kCryptoFiSubcommandShadowRegRead:
      return handle_crypto_fi_shadow_reg_read(uj);
    default:
      LOG_ERROR("Unrecognized Crypto FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
