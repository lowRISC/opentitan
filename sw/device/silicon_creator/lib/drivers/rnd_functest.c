// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/crc32.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_entropy_src_t entropy_src;

// Returns `rnd_threshold` if the target `test_id` supports a low configuration
// threshold, otherwise it returns 0.
static uint32_t random_low_threshold(dif_entropy_src_test_t test_id,
                                     uint32_t rnd_threshold) {
  uint32_t result;
  switch (test_id) {
    case kDifEntropySrcTestRepetitionCount:
    case kDifEntropySrcTestRepetitionCountSymbol:
    case kDifEntropySrcTestBucket:
      result = 0;
      break;
    case kDifEntropySrcTestAdaptiveProportion:
    case kDifEntropySrcTestMarkov:
    case kDifEntropySrcTestMailbox:
      result = rnd_threshold;
      break;
    default:
      CHECK(false, "Unexpected dif_entropy_src_test_t %d", test_id);
      return 0;
  }
  return result;
}

// Configures entropy_src with random but harmless health test thresholds. The
// entropy complex is enabled in continuous mode to generate the random values,
// and then re-enabled to run with the configured health thresholds.
static void configure_random_health_checks(void) {
  // Generate random values using entropy complex in continuous mode.
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
  dif_entropy_src_health_test_config_t configs[kDifEntropySrcTestNumVariants];
  for (uint32_t test_id = kDifEntropySrcTestRepetitionCount;
       test_id < kDifEntropySrcTestNumVariants; ++test_id) {
    // Randomize threshold values without aiming to disrrupt the default
    // entropy_src health test behavior.
    uint32_t meaningless_threshold =
        rand_testutils_gen32_range(/*min=*/0, /*max=*/16);
    configs[test_id] = (dif_entropy_src_health_test_config_t){
        .test_type = (dif_entropy_src_test_t)test_id,
        .high_threshold = 0xFFFFFF00 ^ meaningless_threshold,
        .low_threshold = random_low_threshold(test_id, meaningless_threshold),
    };
  }

  // Configure health values after disabling the entropy complex.
  CHECK_STATUS_OK(entropy_testutils_stop_all());
  for (size_t i = 0; i < ARRAYSIZE(configs); ++i) {
    CHECK_DIF_OK(
        dif_entropy_src_health_test_configure(&entropy_src, configs[i]));
  }
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
}

// Configures the entropy source health check and alert thresholds with the
// configuration stored in OTP.
static void configure_health_checks_from_otp(void) {
  CHECK_STATUS_OK(entropy_testutils_stop_all());
  dif_entropy_src_health_test_config_t configs[] = {
      [kDifEntropySrcTestRepetitionCount] =
          {
              .test_type = kDifEntropySrcTestRepetitionCount,
              .high_threshold = otp_read32(
                  OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_REPCNT_THRESHOLDS_OFFSET),
              .low_threshold = 0,
          },
      [kDifEntropySrcTestRepetitionCountSymbol] =
          {
              .test_type = kDifEntropySrcTestRepetitionCountSymbol,
              .high_threshold = otp_read32(
                  OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_REPCNTS_THRESHOLDS_OFFSET),
              .low_threshold = 0,
          },
      [kDifEntropySrcTestAdaptiveProportion] =
          {
              .test_type = kDifEntropySrcTestAdaptiveProportion,
              .high_threshold = otp_read32(
                  OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_ADAPTP_HI_THRESHOLDS_OFFSET),
              .low_threshold = otp_read32(
                  OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_ADAPTP_LO_THRESHOLDS_OFFSET),
          },
      [kDifEntropySrcTestBucket] =
          {
              .test_type = kDifEntropySrcTestBucket,
              .high_threshold = otp_read32(
                  OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_BUCKET_THRESHOLDS_OFFSET),
              .low_threshold = 0,
          },
      [kDifEntropySrcTestMarkov] =
          {
              .test_type = kDifEntropySrcTestMarkov,
              .high_threshold = otp_read32(
                  OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_MARKOV_HI_THRESHOLDS_OFFSET),
              .low_threshold = otp_read32(
                  OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_MARKOV_LO_THRESHOLDS_OFFSET),
          },
      [kDifEntropySrcTestMailbox] =
          {
              .test_type = kDifEntropySrcTestMailbox,
              .high_threshold = otp_read32(
                  OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EXTHT_HI_THRESHOLDS_OFFSET),
              .low_threshold = otp_read32(
                  OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EXTHT_LO_THRESHOLDS_OFFSET),
          },
  };
  for (size_t i = 0; i < ARRAYSIZE(configs); ++i) {
    CHECK_DIF_OK(
        dif_entropy_src_health_test_configure(&entropy_src, configs[i]));
  }

  // The entropy_src DIF expects the alert threshold to be set at configuration
  // time. We skip enabling csrng and edn0/1 in this case.
  dif_entropy_src_config_t entropy_src_config =
      entropy_testutils_config_default();
  entropy_src_config.alert_threshold = (uint16_t)otp_read32(
      OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_ALERT_THRESHOLD_OFFSET);
  CHECK_DIF_OK(dif_entropy_src_configure(&entropy_src, entropy_src_config,
                                         kDifToggleEnabled));
}

// Checks that the CRC value stored in OTP is consistent with what ROM is
// expecting.
rom_error_t test_otp_crc_check(void) {
  uint32_t ctx;
  crc32_init(&ctx);
  uint32_t otp_in_order_offsets[] = {
      OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_REPCNT_THRESHOLDS_OFFSET,
      OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_REPCNTS_THRESHOLDS_OFFSET,
      OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_ADAPTP_HI_THRESHOLDS_OFFSET,
      OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_ADAPTP_LO_THRESHOLDS_OFFSET,
      OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_BUCKET_THRESHOLDS_OFFSET,
      OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_MARKOV_HI_THRESHOLDS_OFFSET,
      OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_MARKOV_LO_THRESHOLDS_OFFSET,
      OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EXTHT_HI_THRESHOLDS_OFFSET,
      OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EXTHT_LO_THRESHOLDS_OFFSET,
      OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_ALERT_THRESHOLD_OFFSET,
  };
  for (size_t i = 0; i < ARRAYSIZE(otp_in_order_offsets); ++i) {
    crc32_add32(&ctx, otp_read32(otp_in_order_offsets[i]));
  }
  uint32_t crc = crc32_finish(&ctx);
  uint32_t expected = crc ^ kErrorOk;
  uint32_t got =
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_HEALTH_CONFIG_DIGEST_OFFSET);
  CHECK(expected == got, "Unexpected OTP CRC value. expected: 0x%x, got: 0x%x",
        expected, got);

  // If calculated properly, this will return kErrorOk.
  return crc ^ got;
}

rom_error_t test_rnd_health_config_check(void) {
  // The default OTP image uses the default reset configuration. We test that
  // first here because the health tests configuration cannot be reset by
  // toggling the entropy_src enable field. The
  // `configure_random_health_checks()` function called later reduces the health
  // test window sizes.

  // Other lc states must match the expected CRC stored in OTP.
  lifecycle_state_t lc_expect_check[] = {
      kLcStateDev,
      kLcStateProd,
      kLcStateProdEnd,
      kLcStateRma,
  };
  configure_health_checks_from_otp();
  for (size_t i = 0; i < ARRAYSIZE(lc_expect_check); ++i) {
    rom_error_t res = rnd_health_config_check(lc_expect_check[i]);
    CHECK(res == kErrorOk, "Lifecycle: %d, error: %d", lc_expect_check[i], res);
  }

  // Don't care lc states should always return `kErrorOk` regardless of what
  // values are stored in the entropy_src.
  lifecycle_state_t lc_expect_check_skip[] = {
      kLcStateTest,
  };
  configure_random_health_checks();
  for (size_t i = 0; i < ARRAYSIZE(lc_expect_check_skip); ++i) {
    CHECK(rnd_health_config_check(lc_expect_check_skip[i]) == kErrorOk);
  }

  // Configure entropy source one last time to leave the device in a good end
  // state.
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
  return kErrorOk;
}

rom_error_t test_rnd(void) {
  const size_t kTestNumIter = 5;
  uint32_t prev = rnd_uint32();
  uint32_t error_cnt = 0;
  for (size_t i = 0; i < kTestNumIter; ++i) {
    uint32_t got = rnd_uint32();
    if (got == prev) {
      LOG_ERROR("Unexpected duplicate random number: 0x%x.", got);
      error_cnt += 1;
    }
    prev = got;
  }
  if (error_cnt > 0) {
    LOG_ERROR("rnd_test failed, expected: 0 errors, got: %d.", error_cnt);
    return kErrorUnknown;
  }
  return kErrorOk;
}

bool test_main(void) {
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));

  status_t result = OK_STATUS();
  EXECUTE_TEST(result, test_rnd);
  EXECUTE_TEST(result, test_otp_crc_check);
  EXECUTE_TEST(result, test_rnd_health_config_check);
  return status_ok(result);
}
