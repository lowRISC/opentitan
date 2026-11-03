// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "hw/top/dt/hmac.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_keymgr_dpe.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/keymgr_dpe_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top/hmac_regs.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

// HMAC error code reported when the configuration is invalid, which includes
// an invalid sideload key and context switching with a sideloaded key.
static const uint32_t kHmacErrSwInvalidConfig = 0x06;

// The message is the same as in `hmac_smoketest`. The DV environment computes
// the expected digest over the same message, so keep both in sync.
OT_NONSTRING static const char kData[142] =
    "Every one suspects himself of at least one of the cardinal virtues, and "
    "this is mine: I am one of the few honest people that I have ever known";

// Software key and the expected HMAC-SHA256 digest of `kData` for that key.
// The software key is written into the KEY registers first, which must then
// be ignored once the sideloaded key is used.
static uint32_t kHmacKey[8] = {0xec4e6c89, 0x082efa98, 0x299f31d0, 0xa4093822,
                               0x03707344, 0x13198a2e, 0x85a308d3, 0x243f6a88};

static const dif_hmac_digest_t kExpectedSwKeyDigest = {
    .digest = {0xebce4019, 0x284d39f1, 0x5eae12b0, 0x0c48fb23, 0xfadb9531,
               0xafbbf3c2, 0x90d3833f, 0x397b98e4}};

static const dif_hmac_transaction_t kSwKeyConfig = {
    .digest_endianness = kDifHmacEndiannessLittle,
    .message_endianness = kDifHmacEndiannessLittle,
    .sideload = false};

static const dif_hmac_transaction_t kSideloadConfig = {
    .digest_endianness = kDifHmacEndiannessLittle,
    .message_endianness = kDifHmacEndiannessLittle,
    .sideload = true};

static dif_keymgr_dpe_t keymgr_dpe;
static dif_kmac_t kmac;
static dif_hmac_t hmac;

// This is computed and filled by the DV side. It uses the same layout as
// `dif_hmac_digest_t`.
static volatile const uint32_t sideload_digest_result[8] = {0};

/**
 * Wait until HMAC signals `hmac_done` and read the digest.
 *
 * `dif_hmac_finish()` returns as soon as the message FIFO is empty, which can
 * be before the digest is available. With a sideloaded key, the digest reads
 * as zero until the operation has completed, so explicitly wait for done.
 */
OT_WARN_UNUSED_RESULT
static status_t wait_done_and_read_digest(dif_hmac_digest_t *digest) {
  uint32_t usec;
  TRY(compute_hmac_testutils_finish_timeout_usec(&usec));
  IBEX_TRY_SPIN_FOR(
      mmio_region_get_bit32(hmac.base_addr, HMAC_INTR_STATE_REG_OFFSET,
                            HMAC_INTR_STATE_HMAC_DONE_BIT),
      usec);
  TRY(dif_hmac_finish(&hmac, /*disable_after_done=*/true, digest));
  return OK_STATUS();
}

/**
 * Check that HMAC reported `SwInvalidConfig` and clear the error interrupt.
 */
static void check_and_clear_invalid_config_error(void) {
  CHECK(mmio_region_get_bit32(hmac.base_addr, HMAC_INTR_STATE_REG_OFFSET,
                              HMAC_INTR_STATE_HMAC_ERR_BIT),
        "Expected the hmac_err interrupt to be set");
  uint32_t err_code =
      mmio_region_read32(hmac.base_addr, HMAC_ERR_CODE_REG_OFFSET);
  CHECK(err_code == kHmacErrSwInvalidConfig,
        "Unexpected error code 0x%x, expected 0x%x", err_code,
        kHmacErrSwInvalidConfig);
  mmio_region_write32(hmac.base_addr, HMAC_INTR_STATE_REG_OFFSET,
                      1u << HMAC_INTR_STATE_HMAC_ERR_BIT);
}

/**
 * Run HMAC with the software key and check the known-answer digest.
 */
static void run_hmac_with_sw_key(void) {
  CHECK_DIF_OK(
      dif_hmac_mode_hmac_start(&hmac, (uint8_t *)kHmacKey, kSwKeyConfig));
  CHECK_STATUS_OK(hmac_testutils_push_message(&hmac, kData, sizeof(kData)));
  CHECK_STATUS_OK(hmac_testutils_fifo_empty_polled(&hmac));
  CHECK_DIF_OK(dif_hmac_process(&hmac));

  dif_hmac_digest_t digest;
  CHECK_STATUS_OK(wait_done_and_read_digest(&digest));
  CHECK_ARRAYS_EQ(digest.digest, kExpectedSwKeyDigest.digest,
                  ARRAYSIZE(digest.digest));
}

/**
 * Run HMAC with the sideloaded key.
 *
 * While the operation is in progress, check that:
 * - the key length reads back as the width of the sideload interface,
 * - the intermediate digest reads as zero, and
 * - saving the context with `CMD.hash_stop` is rejected and has no effect.
 */
static void run_hmac_with_sideload_key(dif_hmac_digest_t *digest) {
  CHECK_DIF_OK(dif_hmac_mode_hmac_start(&hmac, NULL, kSideloadConfig));

  uint32_t cfg = mmio_region_read32(hmac.base_addr, HMAC_CFG_REG_OFFSET);
  CHECK(bitfield_field32_read(cfg, HMAC_CFG_KEY_LENGTH_FIELD) ==
            HMAC_CFG_KEY_LENGTH_VALUE_KEY_512,
        "Key length must be forced to the sideload key width");

  CHECK_STATUS_OK(hmac_testutils_push_message(&hmac, kData, sizeof(kData)));
  CHECK_STATUS_OK(hmac_testutils_fifo_empty_polled(&hmac));

  for (uint32_t i = 0; i < ARRAYSIZE(digest->digest); ++i) {
    uint32_t word = mmio_region_read32(
        hmac.base_addr,
        HMAC_DIGEST_0_REG_OFFSET + (ptrdiff_t)(i * sizeof(uint32_t)));
    CHECK(word == 0, "Intermediate digest word %d is not zero", i);
  }

  mmio_region_write32(hmac.base_addr, HMAC_CMD_REG_OFFSET,
                      1u << HMAC_CMD_HASH_STOP_BIT);
  check_and_clear_invalid_config_error();

  CHECK_DIF_OK(dif_hmac_process(&hmac));
  CHECK_STATUS_OK(wait_done_and_read_digest(digest));
}

/**
 * Generate the HMAC sideload key from the CreatorRootKey.
 */
static void generate_sideload_key(void) {
  dif_keymgr_dpe_generate_params_t sideload_params = kKeyVersionedParams;
  sideload_params.key_dest = kDifKeymgrDpeKeyDestHmac;
  sideload_params.sideload_key = true;
  // Ensure the slot matches with the CreatorRootKey
  sideload_params.slot_src_sel = kCreatorRootKeyParams.slot_dst_sel;

  // Check the applied key version
  uint32_t max_key_version = kCreatorRootKeyParams.max_key_version;
  if (sideload_params.version > max_key_version) {
    LOG_INFO("Key version %d is greater than the maximum key version %d!",
             sideload_params.version, max_key_version);
    LOG_INFO("Setting key version to the maximum key version %d.",
             max_key_version);
    sideload_params.version = max_key_version;
  }

  CHECK_STATUS_OK(
      keymgr_dpe_testutils_generate_key(&keymgr_dpe, &sideload_params));
}

static bool test_hmac_with_sideloaded_key(void) {
  CHECK_DIF_OK(dif_hmac_init_from_dt(kDtHmac, &hmac));

  // Check that HMAC works with the software key. This also leaves the
  // software key in the KEY registers.
  run_hmac_with_sw_key();
  LOG_INFO("Computed HMAC output for software key.");

  generate_sideload_key();
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated HW output for HMAC from the CreatorRootKey");

  dif_hmac_digest_t sideload_digest_good0;
  run_hmac_with_sideload_key(&sideload_digest_good0);
  LOG_INFO("Computed HMAC output for sideloaded key.");

  // The software key in the KEY registers must not have been used.
  CHECK_ARRAYS_NE(sideload_digest_good0.digest, kExpectedSwKeyDigest.digest,
                  ARRAYSIZE(sideload_digest_good0.digest));

  if (kDeviceType == kDeviceSimDV) {
    // From the DV environment we get the expected digest, so check that the
    // output using the sideloaded key matches the expectation.  We cannot do
    // this check outside the DV environment because we cannot observe the
    // sideloaded key, thus cannot compute the expected digest.
    CHECK_ARRAYS_EQ(sideload_digest_good0.digest,
                    (uint32_t *)sideload_digest_result,
                    ARRAYSIZE(sideload_digest_good0.digest));
  }

  // Clear the sideloaded HMAC key
  LOG_INFO("Clearing the sideloaded key.");
  CHECK_STATUS_OK(keymgr_dpe_testutils_clear_sideload_key(
      &keymgr_dpe, kDifKeymgrDpeSideLoadClearHmac));

  // Stop loading new randomness into the HMAC key port
  CHECK_STATUS_OK(keymgr_dpe_testutils_clear_sideload_key(
      &keymgr_dpe, kDifKeymgrDpeSideLoadClearNone));
  LOG_INFO("Disable clearing of the generated sideload keys.");

  // Starting HMAC with an invalid sideload key must be blocked.
  CHECK_DIF_OK(dif_hmac_mode_hmac_start(&hmac, NULL, kSideloadConfig));
  check_and_clear_invalid_config_error();
  CHECK(!mmio_region_get_bit32(hmac.base_addr, HMAC_INTR_STATE_REG_OFFSET,
                               HMAC_INTR_STATE_HMAC_DONE_BIT),
        "HMAC must not complete with an invalid sideload key");
  // Disable HMAC again so that the next operation starts from a clean state.
  mmio_region_write32(hmac.base_addr, HMAC_CFG_REG_OFFSET, 0);
  LOG_INFO("Ran HMAC with an invalid sideload key and checked that it fails.");

  // Sideload the same HMAC key again and check if we can compute the same
  // result as before.
  generate_sideload_key();
  LOG_INFO("KeymgrDpe regenerated HW output for HMAC from the CreatorRootKey");

  dif_hmac_digest_t sideload_digest_good1;
  run_hmac_with_sideload_key(&sideload_digest_good1);
  LOG_INFO("Re-computed HMAC output for sideloaded key.");

  CHECK_ARRAYS_EQ(sideload_digest_good1.digest, sideload_digest_good0.digest,
                  ARRAYSIZE(sideload_digest_good1.digest));

  return true;
}

bool test_main(void) {
  CHECK_STATUS_OK(keymgr_dpe_testutils_startup(&keymgr_dpe, &kmac));
  CHECK_STATUS_OK(keymgr_dpe_testutils_check_state(
      &keymgr_dpe, kDifKeymgrDpeStateAvailable));
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe derived CreatorRootKey and removed the UDS");
  LOG_INFO("KeymgrDpe is ready for the HMAC test!");

  return test_hmac_with_sideloaded_key();
}
