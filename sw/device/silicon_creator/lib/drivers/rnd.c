// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/silicon_creator/lib/drivers/rnd.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/crc32.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include "entropy_src_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "rv_core_ibex_regs.h"

enum {
  kBaseEntropySrc = TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR,
  kBaseIbex = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR,

  // This covers the health threshold registers which are contiguous. The alert
  // threshold register is not included here.
  kNumHealthRegisters = 9,
};

// Check the number of health registers covered by this driver.
static_assert(kNumHealthRegisters ==
                  (ENTROPY_SRC_EXTHT_LO_THRESHOLDS_REG_OFFSET -
                   ENTROPY_SRC_REPCNT_THRESHOLDS_REG_OFFSET) /
                          sizeof(uint32_t) +
                      1,
              "Unexpected entropy_src health register count.");

// Ensure the relative offsets of OTP versus entropy_src registers are
// equivalent. This is imporant as rom_start.S uses a copy function to
// copy the values from OTP into the entropy_src.
#define ASSERT_REG_OFFSET(otp_offset_, entropy_src_offset_)                         \
  static_assert(                                                                    \
      ((otp_offset_)-OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_REPCNT_THRESHOLDS_OFFSET) == \
          ((entropy_src_offset_)-ENTROPY_SRC_REPCNT_THRESHOLDS_REG_OFFSET),         \
      "OTP configuration offset does not match the expected entropy_src "           \
      "register offset")

ASSERT_REG_OFFSET(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_REPCNT_THRESHOLDS_OFFSET,
                  ENTROPY_SRC_REPCNT_THRESHOLDS_REG_OFFSET);
ASSERT_REG_OFFSET(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_REPCNTS_THRESHOLDS_OFFSET,
                  ENTROPY_SRC_REPCNTS_THRESHOLDS_REG_OFFSET);
ASSERT_REG_OFFSET(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_ADAPTP_HI_THRESHOLDS_OFFSET,
                  ENTROPY_SRC_ADAPTP_HI_THRESHOLDS_REG_OFFSET);
ASSERT_REG_OFFSET(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_ADAPTP_LO_THRESHOLDS_OFFSET,
                  ENTROPY_SRC_ADAPTP_LO_THRESHOLDS_REG_OFFSET);
ASSERT_REG_OFFSET(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_BUCKET_THRESHOLDS_OFFSET,
                  ENTROPY_SRC_BUCKET_THRESHOLDS_REG_OFFSET);
ASSERT_REG_OFFSET(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_MARKOV_HI_THRESHOLDS_OFFSET,
                  ENTROPY_SRC_MARKOV_HI_THRESHOLDS_REG_OFFSET);
ASSERT_REG_OFFSET(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_MARKOV_LO_THRESHOLDS_OFFSET,
                  ENTROPY_SRC_MARKOV_LO_THRESHOLDS_REG_OFFSET);
ASSERT_REG_OFFSET(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EXTHT_HI_THRESHOLDS_OFFSET,
                  ENTROPY_SRC_EXTHT_HI_THRESHOLDS_REG_OFFSET);
ASSERT_REG_OFFSET(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EXTHT_LO_THRESHOLDS_OFFSET,
                  ENTROPY_SRC_EXTHT_LO_THRESHOLDS_REG_OFFSET);

/**
 * Calculates CRC32 over the entropy_src health test and alert thresholds.
 */
uint32_t health_config_crc32(void) {
  uint32_t ctx;
  crc32_init(&ctx);

  // Health test thresholds, whose offsets are statically checked.
  uint32_t offset = ENTROPY_SRC_REPCNT_THRESHOLDS_REG_OFFSET;
  for (size_t i = 0; i < kNumHealthRegisters; ++i, offset += sizeof(uint32_t)) {
    crc32_add32(&ctx, abs_mmio_read32(kBaseEntropySrc + offset));
  }
  crc32_add32(&ctx, abs_mmio_read32(kBaseEntropySrc +
                                    ENTROPY_SRC_ALERT_THRESHOLD_REG_OFFSET));
  return crc32_finish(&ctx);
}

rom_error_t rnd_health_config_check(lifecycle_state_t lc_state) {
  if (otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EN_OFFSET) !=
      kHardenedBoolTrue) {
    return kErrorOk;
  }

  uint32_t crc32 = health_config_crc32();
  rom_error_t res = crc32;

  if (launder32(lc_state) == kLcStateTest) {
    res ^= crc32 ^ kErrorOk;
    HARDENED_CHECK_EQ(res, kErrorOk);
    HARDENED_CHECK_EQ(lc_state, kLcStateTest);
    return res;
  }

  res ^=
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_HEALTH_CONFIG_DIGEST_OFFSET);
  if (launder32(res) != kErrorOk) {
    return kErrorRndBadCrc32;
  }

  HARDENED_CHECK_EQ(res, kErrorOk);
  return res;
}

uint32_t rnd_uint32(void) {
  if (otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EN_OFFSET) ==
      kHardenedBoolTrue) {
    // When bit-0 is clear an EDN request for new data for RND_DATA is
    // pending.
    while (!abs_mmio_read32(kBaseIbex + RV_CORE_IBEX_RND_STATUS_REG_OFFSET)) {
    }
  }
  uint32_t mcycle;
  CSR_READ(CSR_REG_MCYCLE, &mcycle);
  return mcycle + abs_mmio_read32(kBaseIbex + RV_CORE_IBEX_RND_DATA_REG_OFFSET);
}
