// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/keymgr.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

static dif_keymgr_t keymgr;

// Key diversification data for testing
static const keymgr_diversification_t kTestDiversification = {
    .salt =
        {
            0x00112233,
            0x44556677,
            0x8899aabb,
            0xccddeeff,
            0x00010203,
            0x04050607,
            0x08090a0b,
            0x0c0d0e0f,
        },
    .version = 0x0,
};

/**
 * Setup keymgr and entropy complex.
 *
 * Run this test before any others.
 */
status_t test_setup(void) {
  dif_kmac_t kmac;

  TRY(keymgr_testutils_initialize(&keymgr, &kmac));

  return entropy_complex_init(kHardenedBoolFalse);
}

/**
 * Test generating a single software-visible key.
 */
status_t sw_single_key_test(void) {
  keymgr_output_t key;
  return keymgr_generate_key_sw(kTestDiversification, kHardenedBoolFalse, &key);
}

/**
 * Test generating a single sideloaded AES key.
 */
status_t aes_basic_test(void) {
  return keymgr_generate_key_aes(kTestDiversification);
}

/**
 * Test generating a single sideloaded KMAC key.
 */
status_t kmac_basic_test(void) {
  return keymgr_generate_key_kmac(kTestDiversification);
}

/**
 * Test generating a single sideloaded OTBN key.
 */
status_t otbn_basic_test(void) {
  return keymgr_generate_key_otbn(kTestDiversification, kHardenedBoolFalse);
}

/**
 * Test generating a single sideloaded OTBN CDI key.
 */
status_t otbn_basic_cdi_test(void) {
  return keymgr_generate_key_otbn(kTestDiversification, kHardenedBoolTrue);
}

/**
 * Check whether two key manager output values are equivalent.
 */
static bool output_equiv(keymgr_output_t key1, keymgr_output_t key2) {
  for (size_t i = 0; i < kKeymgrOutputShareNumWords; i++) {
    uint32_t word1 = key1.share0[i] ^ key1.share1[i];
    uint32_t word2 = key2.share0[i] ^ key2.share1[i];
    if (word1 != word2) {
      return false;
    }
  }
  return true;
}

/**
 * Test generating software-visible keys with different salts.
 */
status_t sw_keys_change_salt_test(void) {
  keymgr_diversification_t div;
  memcpy(div.salt, kTestDiversification.salt, sizeof(div.salt));
  div.version = kTestDiversification.version;

  keymgr_output_t key1;
  TRY(keymgr_generate_key_sw(div, kHardenedBoolFalse, &key1));

  div.salt[0]++;
  keymgr_output_t key2;
  TRY(keymgr_generate_key_sw(div, kHardenedBoolFalse, &key2));

  TRY_CHECK(!output_equiv(key1, key2));

  div.salt[0]--;
  keymgr_output_t key3;
  TRY(keymgr_generate_key_sw(div, kHardenedBoolFalse, &key3));

  TRY_CHECK(output_equiv(key1, key3));
  TRY_CHECK_ARRAYS_NE(key1.share0, key2.share0, sizeof(key1.share0));

  return OK_STATUS();
}

/**
 * Test generating software-visible keys with different versions.
 */
status_t sw_keys_change_version_test(void) {
  uint32_t max_version;
  TRY(keymgr_testutils_max_key_version_get(&keymgr, &max_version));

  if (max_version == 0) {
    LOG_INFO(
        "Max key version locked to 0 by ROM_EXT. Skipping version change "
        "test.");
    return OK_STATUS();
  }

  keymgr_diversification_t div;
  memcpy(div.salt, kTestDiversification.salt, sizeof(div.salt));
  div.version = kTestDiversification.version;

  keymgr_output_t key1;
  TRY(keymgr_generate_key_sw(div, kHardenedBoolFalse, &key1));

  div.version++;
  keymgr_output_t key2;
  TRY(keymgr_generate_key_sw(div, kHardenedBoolFalse, &key2));

  TRY_CHECK(!output_equiv(key1, key2));

  div.version--;
  keymgr_output_t key3;
  TRY(keymgr_generate_key_sw(div, kHardenedBoolFalse, &key3));

  TRY_CHECK(output_equiv(key1, key3));
  TRY_CHECK_ARRAYS_NE(key1.share0, key2.share0, sizeof(key1.share0));

  return OK_STATUS();
}

static status_t run_negative_test(void) {
  LOG_INFO("Running negative tests.");

  keymgr_output_t dummy_key;

  // Test the request of a key derivation with exceeding version
  keymgr_diversification_t bad_version_div = kTestDiversification;
  bad_version_div.version = 0xFFFFFFFF;
  CHECK_STATUS_OK(ottf_alerts_expect_alert_start(
      kTopEarlgreyAlertIdKeymgrRecovOperationErr));
  CHECK(keymgr_generate_key_sw(bad_version_div, kHardenedBoolFalse, &dummy_key)
            .value == OTCRYPTO_RECOV_ERR.value);
  CHECK_STATUS_OK(ottf_alerts_expect_alert_finish(
      kTopEarlgreyAlertIdKeymgrRecovOperationErr));

  // Negative test keymgr_is_idle()
  CHECK_STATUS_OK(ottf_alerts_expect_alert_start(
      kTopEarlgreyAlertIdKeymgrRecovOperationErr));
  abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_START_REG_OFFSET,
                   1 << KEYMGR_START_EN_BIT);
  CHECK(keymgr_generate_key_sw(kTestDiversification, kHardenedBoolFalse,
                               &dummy_key)
            .value == OTCRYPTO_RECOV_ERR.value);
  uint32_t status;
  uint32_t reg;
  do {
    reg = abs_mmio_read32(TOP_EARLGREY_KEYMGR_BASE_ADDR +
                          KEYMGR_OP_STATUS_REG_OFFSET);
    status = bitfield_field32_read(reg, KEYMGR_OP_STATUS_STATUS_FIELD);
  } while (status == KEYMGR_OP_STATUS_STATUS_VALUE_WIP);
  abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_OP_STATUS_REG_OFFSET,
                   reg);
  uint32_t err_code = abs_mmio_read32(TOP_EARLGREY_KEYMGR_BASE_ADDR +
                                      KEYMGR_ERR_CODE_REG_OFFSET);
  abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_ERR_CODE_REG_OFFSET,
                   err_code);
  CHECK_STATUS_OK(ottf_alerts_expect_alert_finish(
      kTopEarlgreyAlertIdKeymgrRecovOperationErr));

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  static status_t result;

  EXECUTE_TEST(result, test_setup);
  EXECUTE_TEST(result, sw_single_key_test);
  EXECUTE_TEST(result, sw_keys_change_salt_test);
  EXECUTE_TEST(result, sw_keys_change_version_test);
  EXECUTE_TEST(result, aes_basic_test);
  EXECUTE_TEST(result, kmac_basic_test);
  EXECUTE_TEST(result, otbn_basic_test);
  EXECUTE_TEST(result, otbn_basic_cdi_test);
  EXECUTE_TEST(result, run_negative_test);

  return status_ok(result);
}
