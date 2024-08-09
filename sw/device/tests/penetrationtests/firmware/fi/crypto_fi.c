// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/crypto_fi.h"

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/penetrationtests/firmware/lib/sca_lib.h"
#include "sw/device/tests/penetrationtests/json/crypto_fi_commands.h"

#include "aes_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"

// NOP macros.
#define NOP1 "addi x0, x0, 0\n"
#define NOP10 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1
#define NOP30 NOP10 NOP10 NOP10

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
// Interface to Ibex.
static dif_rv_core_ibex_t rv_core_ibex;

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
  // Get the test mode.
  crypto_fi_aes_mode_t uj_data;
  TRY(ujson_deserialize_crypto_fi_aes_mode_t(uj, &uj_data));
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Write the key into the AES block. Set and unset the trigger when
  // key_trigger is true.
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kAesWaitTimeout);
  if (uj_data.key_trigger) {
    sca_set_trigger_high();
  }
  TRY(dif_aes_start(&aes, &transaction, &aes_key_shares, NULL));
  // Busy polling because AES_TESTUTILS_WAIT_FOR_STATUS seems to take longer
  // (~100us) as expected.
  while (!aes_testutils_get_status(&aes, kDifAesStatusInputReady))
    ;
  if (uj_data.key_trigger) {
    sca_set_trigger_low();
  }

  // Write the plaintext into the AES block. Set and unset the trigger when
  // plaintext_trigger is true.
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kAesWaitTimeout);
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                                kAesWaitTimeout);
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
  asm volatile(NOP30);
  TRY(dif_aes_trigger(&aes, kDifAesTriggerStart));
  // Busy polling because AES_TESTUTILS_WAIT_FOR_STATUS seems to take longer
  // (~100us) as expected.
  while (!aes_testutils_get_status(&aes, kDifAesStatusOutputValid))
    ;
  asm volatile(NOP30);
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

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send the ciphertext and the alerts back to the host.
  crypto_fi_aes_ciphertext_t uj_output;
  uj_output.err_status = codes;
  memcpy(uj_output.ciphertext, ciphertext.data, 16);
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_crypto_fi_aes_ciphertext_t, uj, &uj_output);
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

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Read device ID and return to host.
  penetrationtest_device_id_t uj_output;
  TRY(sca_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_id_t, uj, &uj_output);

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

  // Static. Set and unset the trigger when static_trigger is true.
  if (uj_data.static_trigger) {
    sca_set_trigger_high();
  }
  asm volatile(NOP30);
  asm volatile(NOP30);
  asm volatile(NOP30);
  if (uj_data.static_trigger) {
    sca_set_trigger_low();
  }

  // Squeeze. Set and unset the trigger when squeeze_trigger is true.
  uint32_t digest[kKmacTestVector.digest_len];
  if (uj_data.squeeze_trigger) {
    sca_set_trigger_high();
  }
  TRY(dif_kmac_squeeze(&kmac, &kmac_operation_state, digest,
                       kKmacTestVector.digest_len, /*processed=*/NULL,
                       /*capacity=*/NULL));
  if (uj_data.squeeze_trigger) {
    sca_set_trigger_low();
  }

  // 2nd Squeeze. This shall enforce a permutation. Any injected fault will
  // result in a completely different digest. Hence, allows for easy detection
  // of an injected fault.
  uint32_t digest_2nd[kKmacTestVector.digest_len];
  TRY(dif_kmac_squeeze(&kmac, &kmac_operation_state, digest_2nd,
                       kKmacTestVector.digest_len, /*processed=*/NULL,
                       /*capacity=*/NULL));

  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

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
  RESP_OK(ujson_serialize_crypto_fi_kmac_digest_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_crypto_fi_kmac_state(ujson_t *uj) {
  // Get the test mode.
  crypto_fi_kmac_mode_t uj_data;
  TRY(ujson_deserialize_crypto_fi_kmac_mode_t(uj, &uj_data));
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

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
  sca_set_trigger_high();
  asm volatile(NOP30);
  asm volatile(NOP30);
  asm volatile(NOP30);
  sca_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

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

  RESP_OK(ujson_serialize_crypto_fi_kmac_state_t, uj, &uj_output);

  TRY(dif_kmac_end(&kmac, &kmac_operation_state));
  return OK_STATUS();
}

status_t handle_crypto_fi_shadow_reg_access(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

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

  sca_set_trigger_high();
  asm volatile(NOP10);
  SHADOW_REG_ACCESS_10(ctrl_reg_kmac_addr, ctrl_reg_kmac)
  SHADOW_REG_ACCESS_10(ctrl_reg_kmac_addr, ctrl_reg_kmac)
  SHADOW_REG_ACCESS_10(ctrl_reg_kmac_addr, ctrl_reg_kmac)
  asm volatile(NOP10);
  sca_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

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
  RESP_OK(ujson_serialize_crypto_fi_test_result_mult_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_crypto_fi_shadow_reg_read(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

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

  sca_set_trigger_high();
  asm volatile(NOP30);
  uint32_t ctrl_reg_aes_read = abs_mmio_read32(TOP_EARLGREY_AES_BASE_ADDR +
                                               AES_CTRL_SHADOWED_REG_OFFSET);
  uint32_t ctrl_reg_kmac_read = abs_mmio_read32(TOP_EARLGREY_KMAC_BASE_ADDR +
                                                KMAC_CFG_SHADOWED_REG_OFFSET);
  asm volatile(NOP30);
  sca_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

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
