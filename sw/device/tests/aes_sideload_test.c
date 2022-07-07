// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"  // Generated.

#define TIMEOUT (1000 * 1000)

static const uint32_t kPlainText[] = {
    0x33221100,
    0x77665544,
    0xbbaa9988,
    0xffeeddcc,
};

enum {
  /** Flash Secret partition ID. */
  kFlashInfoPartitionId = 0,

  /** Secret partition flash bank ID. */
  kFlashInfoBankId = 0,

  /** Creator Secret flash info page ID. */
  kFlashInfoPageIdCreatorSecret = 1,

  /** Owner Secret flash info page ID. */
  kFlashInfoPageIdOwnerSecret = 2,

  /** Key manager secret word size. */
  kSecretWordSize = 8,
};

/**
 * Software binding value for advancing to creator state.
 */
static const dif_keymgr_state_params_t kCreatorParams = {
    .binding_value = {0xdc96c23d, 0xaf36e268, 0xcb68ff71, 0xe92f76e2,
                      0xb8a8379d, 0x426dc745, 0x19f5cff7, 0x4ec9c6d6},
    .max_key_version = 0x11,
};

/**
 * Software binding value for advancing to owner int state.
 */
static const dif_keymgr_state_params_t kOwnerIntParams = {
    .binding_value = {0xe4987b39, 0x3f83d390, 0xc2f3bbaf, 0x3195dbfa,
                      0x23fb480c, 0xb012ae5e, 0xf1394d28, 0x1940ceeb},
    .max_key_version = 0xaa,
};

/**
 * Key manager Creator Secret stored in info flash page.
 */
static const uint32_t kCreatorSecret[kSecretWordSize] = {
    0x4e919d54, 0x322288d8, 0x4bd127c7, 0x9f89bc56,
    0xb4fb0fdf, 0x1ca1567b, 0x13a0e876, 0xa6521d8f};

/**
 * Key manager Owner Secret stored in info flash page.
 */
static const uint32_t kOwnerSecret[kSecretWordSize] = {
    0xa6521d8f, 0x13a0e876, 0x1ca1567b, 0xb4fb0fdf,
    0x9f89bc56, 0x4bd127c7, 0x322288d8, 0x4e919d54,
};

static const dif_keymgr_versioned_key_params_t kKeyVersionedParams = {
    .dest = kDifKeymgrVersionedKeyDestSw,
    .salt =
        {
            0xb6521d8f,
            0x13a0e876,
            0x1ca1567b,
            0xb4fb0fdf,
            0x9f89bc56,
            0x4bd127c7,
            0x322288d8,
            0xde919d54,
        },
    .version = 0xaa,
};
static dif_keymgr_t keymgr;

OTTF_DEFINE_TEST_CONFIG();

static void write_info_page(dif_flash_ctrl_state_t *flash, uint32_t page_id,
                            const uint32_t *data) {
  uint32_t address = flash_ctrl_testutils_info_region_setup(
      flash, page_id, kFlashInfoBankId, kFlashInfoPartitionId);

  CHECK(flash_ctrl_testutils_erase_and_write_page(
            flash, address, kFlashInfoPartitionId, data,
            kDifFlashCtrlPartitionTypeInfo, kSecretWordSize) == 0);

  uint32_t readback_data[kSecretWordSize];
  CHECK(flash_ctrl_testutils_read(flash, address, kFlashInfoPartitionId,
                                  readback_data, kDifFlashCtrlPartitionTypeInfo,
                                  kSecretWordSize, 0) == 0);
  CHECK_ARRAYS_EQ(data, readback_data, kSecretWordSize);
}

static void init_flash(void) {
  dif_flash_ctrl_state_t flash;

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  // Initialize flash secrets.
  write_info_page(&flash, kFlashInfoPageIdCreatorSecret, kCreatorSecret);
  write_info_page(&flash, kFlashInfoPageIdOwnerSecret, kOwnerSecret);
}

static void keymgr_initialize(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR);
  CHECK_DIF_OK(dif_keymgr_init(base_addr, &keymgr));

  keymgr_testutils_check_state(&keymgr, kDifKeymgrStateReset);

  keymgr_testutils_advance_state(&keymgr, NULL);
  keymgr_testutils_check_state(&keymgr, kDifKeymgrStateInitialized);
  LOG_INFO("Keymgr entered Init State");

  keymgr_testutils_advance_state(&keymgr, &kCreatorParams);
  keymgr_testutils_check_state(&keymgr, kDifKeymgrStateCreatorRootKey);
  LOG_INFO("Keymgr entered CreatorRootKey State");

  keymgr_testutils_generate_identity(&keymgr);
  LOG_INFO("Keymgr generated identity at CreatorRootKey State");

  keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams);
  keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerIntermediateKey);
  LOG_INFO("Keymgr entered OwnerIntKey State");

  keymgr_testutils_generate_identity(&keymgr);
  LOG_INFO("Keymgr generated identity at OwnerIntKey State");

  keymgr_testutils_generate_versioned_key(&keymgr, kKeyVersionedParams);
  LOG_INFO("Keymgr generated SW output at OwnerIntKey State");

  dif_keymgr_versioned_key_params_t sideload_params = kKeyVersionedParams;
  sideload_params.dest = kDifKeymgrVersionedKeyDestAes;
  keymgr_testutils_generate_versioned_key(&keymgr, sideload_params);
  LOG_INFO("Keymgr generated HW output for Aes at OwnerIntKey State");
}

void aes_test(void) {
  dif_aes_t aes;
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

  // Setup ECB encryption transaction.
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey256,
      .manual_operation = kDifAesManualOperationManual,
      .masking = kDifAesMaskingInternalPrng,
      .key_provider = kDifAesKeySideload,
      .mask_reseeding = kDifAesReseedPer64Block,
  };

  LOG_INFO("Encrypting the plain text with the side loaded key.");
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, NULL, NULL));
  dif_aes_data_t in_data_plain;
  memcpy(in_data_plain.data, kPlainText, sizeof(kPlainText));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true, TIMEOUT);
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  // Trigger the AES encryption and wait for it to complete.
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusOutputValid, true, TIMEOUT);

  //  Verify that the ciphertext is different from the plaintext.
  dif_aes_data_t out_data;
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data));
  CHECK_ARRAYS_NE(out_data.data, kPlainText, ARRAYSIZE(kPlainText));

  // Finish the ECB encryption transaction.
  CHECK_DIF_OK(dif_aes_end(&aes));

  LOG_INFO("Decrypting the cypher text with the side loaded key.");
  transaction.operation = kDifAesOperationDecrypt;
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, NULL, NULL));
  memcpy(in_data_plain.data, out_data.data, sizeof(out_data.data));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true, TIMEOUT);
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  // Trigger the AES decryption and wait for it to complete.
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusOutputValid, true, TIMEOUT);

  // Verify that the output is equal to the plain text.
  dif_aes_data_t out_data_plain;
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data_plain));
  CHECK_ARRAYS_EQ(out_data_plain.data, kPlainText, ARRAYSIZE(kPlainText));

  // Finish the ECB decryption transaction.
  CHECK_DIF_OK(dif_aes_end(&aes));

  LOG_INFO("Clearing the side loaded key.");

  // Clear the key in the keymgr and decrypt the ciphertext again.
  CHECK_DIF_OK(
      dif_keymgr_sideload_clear_set_enabled(&keymgr, kDifToggleEnabled));
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, NULL, NULL));

  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true, TIMEOUT);
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  // Trigger the AES decryption and wait for it to complete.
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusOutputValid, true, TIMEOUT);

  // Verify that output is not equal to the plain text.
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data_plain));
  CHECK_ARRAYS_NE(out_data_plain.data, kPlainText, ARRAYSIZE(kPlainText));
  CHECK_DIF_OK(dif_aes_end(&aes));
}

static void init_kmac_for_keymgr(void) {
  dif_kmac_t kmac;
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Configure KMAC hardware using software entropy.
  CHECK_DIF_OK(dif_kmac_configure(&kmac, (dif_kmac_config_t){
                                             .sideload = true,
                                         }));
}

bool test_main(void) {
  dif_rstmgr_t rstmgr;
  dif_rstmgr_reset_info_bitfield_t info;

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  rstmgr_testutils_reset_reason(&rstmgr, &info);

  init_flash();

  // POR reset.
  if (info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Powered up for the first time, program flash");

    // Lock otp secret partition.
    dif_otp_ctrl_t otp;
    CHECK_DIF_OK(dif_otp_ctrl_init(
        mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));
    otp_ctrl_testutils_lock_partition(&otp, kDifOtpCtrlPartitionSecret2, 0);

    // Reboot device.
    rstmgr_testutils_reset_reason_clear(&rstmgr);
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));

    // Wait here until device reset.
    wait_for_interrupt();

  } else if (info == kDifRstmgrResetInfoSw) {
    LOG_INFO(
        "Powered up for the second time, actuate keymgr and perform aes test.");

    init_kmac_for_keymgr();

    // Configure the keymgr to generate an aes key.
    keymgr_initialize();

    aes_test();
  }

  return true;
}
