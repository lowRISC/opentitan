// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/crypto_fi.h"

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/penetrationtests/firmware/sca_lib.h"
#include "sw/device/tests/penetrationtests/json/crypto_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  /**
   * Timeout for waiting that an AES operation has completed.
   */
  kAesWaitTimeout = 1000000,
};

static dif_aes_t aes;
static dif_kmac_t kmac;

static dif_aes_key_share_t aes_key_shares;
static dif_aes_data_t aes_plaintext;

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
const kmac_test_t kKmacTestVector = {
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

static const uint8_t kKeyShare1[] = {
    0x0f, 0x1f, 0x2f, 0x3f, 0x4f, 0x5f, 0x6f, 0x7f, 0x8f, 0x9f, 0xaf,
    0xbf, 0xcf, 0xdf, 0xef, 0xff, 0x0a, 0x1a, 0x2a, 0x3a, 0x4a, 0x5a,
    0x6a, 0x7a, 0x8a, 0x9a, 0xaa, 0xba, 0xca, 0xda, 0xea, 0xfa,
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

status_t handle_crypto_fi_aes(ujson_t *uj) {
  // Get the test mode.
  crypto_fi_aes_mode_t uj_data;
  TRY(ujson_deserialize_crypto_fi_aes_mode_t(uj, &uj_data));
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Write the key into the AES block. Set and unset the trigger when
  // key_trigger is true.
  if (uj_data.key_trigger) {
    sca_set_trigger_high();
  }
  TRY(dif_aes_start(&aes, &transaction, &aes_key_shares, NULL));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                                kAesWaitTimeout);
  if (uj_data.key_trigger) {
    sca_set_trigger_low();
  }

  // Write the plaintext into the AES block. Set and unset the trigger when
  // plaintext_trigger is true.
  if (uj_data.plaintext_trigger) {
    sca_set_trigger_high();
  }
  TRY(dif_aes_load_data(&aes, aes_plaintext));
  if (uj_data.plaintext_trigger) {
    sca_set_trigger_low();
  }

  // Start the encryption. Set and unset the trigger when encrypt_trigger is
  // true.
  if (uj_data.encrypt_trigger) {
    sca_set_trigger_high();
  }
  TRY(dif_aes_trigger(&aes, kDifAesTriggerStart));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusOutputValid, true,
                                kAesWaitTimeout);
  if (uj_data.encrypt_trigger) {
    sca_set_trigger_low();
  }

  // Read the ciphertext. Set and unset the trigger when ciphertext_trigger is
  // true.
  dif_aes_data_t ciphertext;
  if (uj_data.ciphertext_trigger) {
    sca_set_trigger_high();
  }
  TRY(dif_aes_read_output(&aes, &ciphertext));
  if (uj_data.ciphertext_trigger) {
    sca_set_trigger_low();
  }

  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Send the ciphertext and the alerts back to the host.
  crypto_fi_aes_ciphertext_t uj_output;
  memcpy(uj_output.ciphertext, ciphertext.data, 16);
  uj_output.alerts_1 = reg_alerts.alerts_1;
  uj_output.alerts_2 = reg_alerts.alerts_2;
  uj_output.alerts_3 = reg_alerts.alerts_3;
  RESP_OK(ujson_serialize_crypto_fi_aes_ciphertext_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_crypto_fi_kmac(ujson_t *uj) {
  // Get the test mode.
  crypto_fi_kmac_mode_t uj_data;
  TRY(ujson_deserialize_crypto_fi_kmac_mode_t(uj, &uj_data));
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Configure and write key to the KMAC block. Set and unset the trigger when
  // key_trigger is true.
  dif_kmac_operation_state_t kmac_operation_state;
  if (uj_data.key_trigger) {
    sca_set_trigger_high();
  }

  TRY(dif_kmac_mode_kmac_start(&kmac, &kmac_operation_state,
                               kKmacTestVector.mode, 0, &kKmacTestVector.key,
                               NULL));
  if (uj_data.key_trigger) {
    sca_set_trigger_low();
  }

  // Absorb. Set and unset the trigger when absorb_trigger is true.
  if (uj_data.absorb_trigger) {
    sca_set_trigger_high();
  }
  TRY(dif_kmac_absorb(&kmac, &kmac_operation_state, kKmacTestVector.message,
                      kKmacTestVector.message_len, NULL));
  if (uj_data.absorb_trigger) {
    sca_set_trigger_low();
  }

  // Squeeze. Set and unset the trigger when squeeze_trigger is true.
  uint32_t digest[kKmacTestVector.digest_len];
  if (uj_data.squeeze_trigger) {
    sca_set_trigger_high();
  }
  TRY(dif_kmac_squeeze(&kmac, &kmac_operation_state, digest,
                       kKmacTestVector.digest_len, /*processed=*/NULL));
  if (uj_data.squeeze_trigger) {
    sca_set_trigger_low();
  }

  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  TRY(dif_kmac_end(&kmac, &kmac_operation_state));

  // Send the first 8 bytes of the digest and the alerts back to the host.
  crypto_fi_kmac_digest_t uj_output;
  memcpy(uj_output.digest, (uint8_t *)digest, 8);
  uj_output.alerts_1 = reg_alerts.alerts_1;
  uj_output.alerts_2 = reg_alerts.alerts_2;
  uj_output.alerts_3 = reg_alerts.alerts_3;
  RESP_OK(ujson_serialize_crypto_fi_kmac_digest_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_crypto_fi_init(ujson_t *uj) {
  sca_select_trigger_type(kScaTriggerTypeSw);
  sca_init(kScaTriggerSourceAes,
           kScaPeripheralIoDiv4 | kScaPeripheralAes | kScaPeripheralKmac |
               kScaPeripheralEdn | kScaPeripheralCsrng | kScaPeripheralEntropy);
  // Configure the alert handler. Alerts triggered by IP blocks are captured
  // and reported to the test.
  sca_configure_alert_handler();

  // Disable the instruction cache and dummy instructions for FI attacks.
  sca_configure_cpu();

  // Init the AES block.
  TRY(dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  TRY(dif_aes_reset(&aes));

  // Mask the AES key.
  uint8_t key_share0[sizeof(kAesModesKey256)];
  for (int i = 0; i < sizeof(kAesModesKey256); ++i) {
    key_share0[i] = kAesModesKey256[i] ^ kKeyShare1[i];
  }
  // "Convert" AES key share byte arrays to `dif_aes_key_share_t`.
  memcpy(aes_key_shares.share0, key_share0, sizeof(aes_key_shares.share0));
  memcpy(aes_key_shares.share1, kKeyShare1, sizeof(aes_key_shares.share1));
  // Copy the plaintext into `dif_aes_data_t`.
  memcpy(aes_plaintext.data, kAesModesPlainText, sizeof(aes_plaintext.data));

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

  return OK_STATUS();
}

status_t handle_crypto_fi(ujson_t *uj) {
  crypto_fi_subcommand_t cmd;
  TRY(ujson_deserialize_crypto_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kCryptoFiSubcommandInit:
      return handle_crypto_fi_init(uj);
    case kCryptoFiSubcommandAes:
      return handle_crypto_fi_aes(uj);
    case kCryptoFiSubcommandKmac:
      return handle_crypto_fi_kmac(uj);
    default:
      LOG_ERROR("Unrecognized Crypto FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
