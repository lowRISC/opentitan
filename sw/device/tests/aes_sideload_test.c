// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
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
static dif_keymgr_t keymgr;

OTTF_DEFINE_TEST_CONFIG();

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

bool test_main(void) {
  dif_rstmgr_t rstmgr;
  dif_rstmgr_reset_info_bitfield_t info;

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  info = rstmgr_testutils_reason_get();

  // POR reset.
  if (info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Powered up for the first time, program flash");

    keymgr_testutils_init_flash();

    // Lock otp secret partition.
    dif_otp_ctrl_t otp;
    CHECK_DIF_OK(dif_otp_ctrl_init(
        mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));
    otp_ctrl_testutils_lock_partition(&otp, kDifOtpCtrlPartitionSecret2, 0);

    // Reboot device.
    rstmgr_testutils_reason_clear();
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));

    // Wait here until device reset.
    wait_for_interrupt();

  } else if (info == kDifRstmgrResetInfoSw) {
    LOG_INFO(
        "Powered up for the second time, actuate keymgr and perform aes test.");

    // Configure the keymgr to generate an aes key.
    keymgr_initialize();

    aes_test();
    return true;
  }

  return false;
}
