// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

#include "hmac_regs.h"

typedef enum hmac_err {

  /**
   * No error has occured.
   */
  kErrorNone = 0x0,

  /**
   * This error is reported when HMAC detects the CMD.start command while SHA is
   * disabled
   */
  kErrorSwHashStartWhenShaDisabled = 0x02,

  /**
   *This error occurs when software attempts to modify the secret key CSRs
   *during hashing
   */
  kErrorSwUpdateSecretKeyInProcess = 0x03,

  /**
   *This error is reported when CMD.start is received while HMAC is running
   */
  kErrorSwHashStartWhenActive = 0x04,

  /**
   *This error is reported when the MSG_FIFO is updated when disallowed
   */
  kErrorSwPushMsgWhenDisallowed = 0x05,

  /**
   *This error is reported when HMAC has been configured incorrectly by software
   */
  kErrorSwInvalidConfig = 0x06,

} hmac_error_t;

static const dif_hmac_transaction_t kHmacTransactionConfig = {
    .digest_endianness = kDifHmacEndiannessLittle,
    .message_endianness = kDifHmacEndiannessLittle,
};

static const char kData[142] =
    "Every one suspects himself of at least one of "
    "the cardinal virtues, and this is mine: I am "
    "one of the few honest people that I have ever "
    "known";

static uint32_t kHmacKey[8] = {
    0xec4e6c89, 0x082efa98, 0x299f31d0, 0xa4093822,
    0x03707344, 0x13198a2e, 0x85a308d3, 0x243f6a88,
};

static const dif_hmac_digest_t kExpectedShaDigest = {
    .digest =
        {
            0xd6c6c94e,
            0xf7cff519,
            0x45c76d42,
            0x9d37a8b8,
            0xe2762fe9,
            0x71ff68cb,
            0x68e236af,
            0x3dc296dc,
        },
};

static const dif_hmac_digest_t kExpectedHmacDigest = {
    .digest =
        {
            0xebce4019,
            0x284d39f1,
            0x5eae12b0,
            0x0c48fb23,
            0xfadb9531,
            0xafbbf3c2,
            0x90d3833f,
            0x397b98e4,
        },
};

/**
 * Initialize the HMAC engine. Return `true` if the configuration is valid.
 */
static void test_setup(mmio_region_t base_addr, dif_hmac_t *hmac) {
  CHECK_DIF_OK(dif_hmac_init(base_addr, hmac));
}

/**
 * Start HMAC in the correct mode. If `key` == NULL use SHA256 mode, otherwise
 * use the provided key in HMAC mode.
 */

static void test_start(const dif_hmac_t *hmac, const uint8_t *key) {
  // Let a null key indicate we are operating in SHA256-only mode.
  if (key == NULL) {
    CHECK_DIF_OK(dif_hmac_mode_sha256_start(hmac, kHmacTransactionConfig));
  } else {
    CHECK_DIF_OK(dif_hmac_mode_hmac_start(hmac, key, kHmacTransactionConfig));
  }
}

/**
 * Kick off the HMAC (or SHA256) run.
 */
static void run_hmac(const dif_hmac_t *hmac) {
  CHECK_DIF_OK(dif_hmac_process(hmac));
}

static void run_hmac_enable_interrupt(void) {
  // Enable Interrupt enable register
  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, HMAC_INTR_ENABLE_HMAC_DONE_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_INTR_ENABLE_FIFO_EMPTY_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_INTR_ENABLE_HMAC_ERR_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_ENABLE_REG_OFFSET,
                   reg);
}

static void run_hmac_clear_interrupt(void) {
  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, HMAC_INTR_STATE_HMAC_DONE_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_INTR_STATE_FIFO_EMPTY_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_INTR_STATE_HMAC_ERR_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET,
                   reg);
}

// The following function reports error when attempts to write data into the
// message FIFO (MSG_FIFO) while the SHA engine is disabled.
status_t run_test_pushmsg_when_shadisabled(
    const dif_hmac_t *hmac, const char *data, size_t len, const uint8_t *key,
    const dif_hmac_digest_t *expected_digest) {
  run_hmac_enable_interrupt();
  // Read current config register
  uint32_t cfg_reg_3 =
      abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET);
  // Disable SHA_EN
  cfg_reg_3 = bitfield_bit32_write(cfg_reg_3, HMAC_CFG_SHA_EN_BIT, false);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET,
                   cfg_reg_3);
  CHECK_STATUS_OK(hmac_testutils_push_message(hmac, data, len));
  uint32_t hmac_err_reg =
      mmio_region_read32(hmac->base_addr, HMAC_ERR_CODE_REG_OFFSET);
  TRY_CHECK(hmac_err_reg == kErrorSwPushMsgWhenDisallowed,
            "Error code doesn't match expected code ");
  run_hmac_clear_interrupt();
  return OK_STATUS();
}

// The following function reports error when attempts to write data into the
// message FIFO (MSG_FIFO) when hmac is already in process
status_t run_test_pushmsg_when_disallowed(
    const dif_hmac_t *hmac, const char *data, size_t len, const uint8_t *key,
    const dif_hmac_digest_t *expected_digest) {
  run_hmac_enable_interrupt();
  test_start(hmac, key);
  CHECK_STATUS_OK(hmac_testutils_push_message(hmac, data, len));
  CHECK_STATUS_OK(hmac_testutils_fifo_empty_polled(hmac));
  run_hmac(hmac);
  CHECK_STATUS_OK(hmac_testutils_push_message(hmac, data, len));
  uint32_t hmac_err_reg =
      mmio_region_read32(hmac->base_addr, HMAC_ERR_CODE_REG_OFFSET);
  TRY_CHECK(hmac_err_reg == kErrorSwPushMsgWhenDisallowed,
            "Error code doesn't match expected code");
  CHECK_STATUS_OK(hmac_testutils_fifo_empty_polled(hmac));
  run_hmac_clear_interrupt();
  return OK_STATUS();
}
// The following function reports error when the HMAC has been incorrectly
// configured by software. This could include an invalid key length for HMAC
// mode
status_t run_test_invalidconfig_keylength(
    const dif_hmac_t *hmac, const char *data, size_t len, const uint8_t *key,
    const dif_hmac_digest_t *expected_digest) {
  run_hmac_enable_interrupt();
  // Set HMAC KeyLength to Key_none  and SHA2/HMAC Digest size to SHA2_256
  uint32_t reg = 0;
  reg = bitfield_field32_write(reg, HMAC_CFG_KEY_LENGTH_FIELD,
                               HMAC_CFG_KEY_LENGTH_VALUE_KEY_NONE);
  reg = bitfield_field32_write(reg, HMAC_CFG_DIGEST_SIZE_FIELD,
                               HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_256);
  reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, reg);
  uint32_t hmac_cmd_reg =
      mmio_region_read32(hmac->base_addr, HMAC_CMD_REG_OFFSET);
  hmac_cmd_reg =
      bitfield_bit32_write(hmac_cmd_reg, HMAC_CMD_HASH_START_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET,
                   hmac_cmd_reg);
  uint32_t hmacerr_reg =
      mmio_region_read32(hmac->base_addr, HMAC_ERR_CODE_REG_OFFSET);
  TRY_CHECK(hmacerr_reg == kErrorSwInvalidConfig,
            "Error code doesn't match expected code");
  CHECK_STATUS_OK(hmac_testutils_push_message(hmac, data, len));
  CHECK_STATUS_OK(hmac_testutils_fifo_empty_polled(hmac));
  run_hmac(hmac);
  hmac_cmd_reg = mmio_region_read32(hmac->base_addr, HMAC_CMD_REG_OFFSET);
  hmac_cmd_reg =
      bitfield_bit32_write(hmac_cmd_reg, HMAC_CMD_HASH_STOP_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET,
                   hmac_cmd_reg);
  // Write default cfg reg values to clear the error
  uint32_t cfg_reg_default = HMAC_CFG_REG_RESVAL;
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET,
                   cfg_reg_default);
  run_hmac_clear_interrupt();
  return OK_STATUS();
}

// The following function reports error is reported when the HMAC has been
// incorrectly configured by software. This could include an invalid digest size
// for SHA-2/HMAC modes or an invalid key length for HMAC mode
status_t run_test_invalidconfig_digest(
    const dif_hmac_t *hmac, const char *data, size_t len, const uint8_t *key,
    const dif_hmac_digest_t *expected_digest) {
  run_hmac_enable_interrupt();
  // Set HMAC KeyLength to 256 bit  and SHA2/HMAC Digest size to SHA2_None
  uint32_t reg = 0;
  reg = bitfield_field32_write(reg, HMAC_CFG_KEY_LENGTH_FIELD,
                               HMAC_CFG_KEY_LENGTH_VALUE_KEY_256);
  reg = bitfield_field32_write(reg, HMAC_CFG_DIGEST_SIZE_FIELD,
                               HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_NONE);
  reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, reg);
  uint32_t hmac_cmd_reg =
      mmio_region_read32(hmac->base_addr, HMAC_CMD_REG_OFFSET);
  hmac_cmd_reg =
      bitfield_bit32_write(hmac_cmd_reg, HMAC_CMD_HASH_START_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET,
                   hmac_cmd_reg);
  uint32_t hmacerr_reg =
      mmio_region_read32(hmac->base_addr, HMAC_ERR_CODE_REG_OFFSET);
  TRY_CHECK(hmacerr_reg == kErrorSwInvalidConfig,
            "Error code doesn't match expected code");
  CHECK_STATUS_OK(hmac_testutils_push_message(hmac, data, len));
  CHECK_STATUS_OK(hmac_testutils_fifo_empty_polled(hmac));
  run_hmac(hmac);
  hmac_cmd_reg = mmio_region_read32(hmac->base_addr, HMAC_CMD_REG_OFFSET);
  hmac_cmd_reg =
      bitfield_bit32_write(hmac_cmd_reg, HMAC_CMD_HASH_STOP_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET,
                   hmac_cmd_reg);
  // Write default cfg reg values to clear the error
  uint32_t cfg_reg_default = HMAC_CFG_REG_RESVAL;
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET,
                   cfg_reg_default);
  run_hmac_clear_interrupt();
  return OK_STATUS();
}

// The following function reports error is reported when the HMAC has been
// incorrectly configured by software. This could include an invalid digest size
// for SHA-2/HMAC modes or an invalid key length for HMAC mode
status_t run_test_updatekey(const dif_hmac_t *hmac, const char *data,
                            size_t len, const uint8_t *key,
                            const dif_hmac_digest_t *expected_digest) {
  run_hmac_enable_interrupt();
  test_start(hmac, key);
  CHECK_STATUS_OK(hmac_testutils_push_message(hmac, data, len));
  CHECK_STATUS_OK(hmac_testutils_fifo_empty_polled(hmac));
  // Updating the config with swap key - while hmac engine is in process state
  CHECK_DIF_OK(dif_hmac_mode_hmac_start(hmac, key, kHmacTransactionConfig));
  uint32_t hmacerr_reg =
      mmio_region_read32(hmac->base_addr, HMAC_ERR_CODE_REG_OFFSET);
  TRY_CHECK(hmacerr_reg == kErrorSwUpdateSecretKeyInProcess,
            "Error code doesn't match expected code");
  run_hmac(hmac);
  run_hmac_clear_interrupt();
  return OK_STATUS();
}

//   Reported when CMD.start is received when SHA is disabled
status_t run_test_hashstartwhendisabled(
    const dif_hmac_t *hmac, const char *data, size_t len, const uint8_t *key,
    const dif_hmac_digest_t *expected_digest) {
  run_hmac_enable_interrupt();
  uint32_t cfg_reg =
      abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET);
  // Disable SHA_EN
  cfg_reg = bitfield_bit32_write(cfg_reg, HMAC_CFG_SHA_EN_BIT, false);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, cfg_reg);
  // Write HASH_START_BIT
  uint32_t hmac_cmd_reg =
      mmio_region_read32(hmac->base_addr, HMAC_CMD_REG_OFFSET);
  hmac_cmd_reg =
      bitfield_bit32_write(hmac_cmd_reg, HMAC_CMD_HASH_START_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET,
                   hmac_cmd_reg);
  uint32_t hmacerr_reg =
      mmio_region_read32(hmac->base_addr, HMAC_ERR_CODE_REG_OFFSET);
  TRY_CHECK(hmacerr_reg == kErrorSwHashStartWhenShaDisabled,
            "Error code doesn't match expected code");
  run_hmac_clear_interrupt();
  return OK_STATUS();
}

//   Reported when CMD.start is received while the HMAC is running
status_t run_test_hashstartwhenactive(
    const dif_hmac_t *hmac, const char *data, size_t len, const uint8_t *key,
    const dif_hmac_digest_t *expected_digest) {
  run_hmac_enable_interrupt();
  test_start(hmac, key);
  uint32_t hmac_cmd_reg =
      mmio_region_read32(hmac->base_addr, HMAC_CMD_REG_OFFSET);
  hmac_cmd_reg =
      bitfield_bit32_write(hmac_cmd_reg, HMAC_CMD_HASH_START_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET,
                   hmac_cmd_reg);
  uint32_t hmac_err_reg =
      mmio_region_read32(hmac->base_addr, HMAC_ERR_CODE_REG_OFFSET);
  TRY_CHECK(hmac_err_reg == kErrorSwHashStartWhenActive,
            "Error code doesn't match expected code");
  run_hmac(hmac);
  run_hmac_clear_interrupt();
  return OK_STATUS();
}

bool test_main(void) {
  LOG_INFO("Running HMAC Error Condition test...");

  dif_hmac_t hmac;
  test_setup(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR), &hmac);
  LOG_INFO("Running test push message when sha disabled...");
  run_test_pushmsg_when_shadisabled(&hmac, kData, sizeof(kData), NULL,
                                    &kExpectedHmacDigest);

  LOG_INFO("Running Hash start test  when sha is disabled...");
  run_test_hashstartwhendisabled(&hmac, kData, sizeof(kData), NULL,
                                 &kExpectedShaDigest);

  LOG_INFO("Running test with key when disallowed..,");
  run_test_updatekey(&hmac, kData, sizeof(kData), (uint8_t *)(&kHmacKey[0]),
                     &kExpectedHmacDigest);

  LOG_INFO("Running test HMAC hash start when active...");
  run_test_hashstartwhenactive(&hmac, kData, sizeof(kData),
                               (uint8_t *)(&kHmacKey[0]), &kExpectedHmacDigest);

  LOG_INFO("Running test push message when  disallowed...");
  run_test_pushmsg_when_disallowed(&hmac, kData, sizeof(kData),
                                   (uint8_t *)(&kHmacKey[0]),
                                   &kExpectedHmacDigest);

  LOG_INFO("Running test HMAC invalid config keylength...");
  run_test_invalidconfig_keylength(&hmac, kData, sizeof(kData),
                                   (uint8_t *)(&kHmacKey[0]),
                                   &kExpectedHmacDigest);

  LOG_INFO("Running test HMAC hash start when active...");
  run_test_hashstartwhenactive(&hmac, kData, sizeof(kData),
                               (uint8_t *)(&kHmacKey[0]), &kExpectedHmacDigest);

  LOG_INFO("Running test HMAC invalid config digest size...");
  run_test_invalidconfig_digest(&hmac, kData, sizeof(kData),
                                (uint8_t *)(&kHmacKey[0]),
                                &kExpectedHmacDigest);

  return true;
}
