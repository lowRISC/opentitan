// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/rnd.h"

#include "hw/top/dt/entropy_src.h"
#include "hw/top/dt/rv_core_ibex.h"
#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include "hw/top/entropy_src_regs.h"
#include "hw/top/otp_ctrl_regs.h"
#include "hw/top/rv_core_ibex_regs.h"

enum {
  // This covers the health threshold registers which are contiguous. The alert
  // threshold register is not included here.
  kNumHealthRegisters = 9,
};

static inline uint32_t entropy_src_base(void) {
  return dt_entropy_src_primary_reg_block(kDtEntropySrc);
}

static inline uint32_t ibex_base(void) {
  return dt_rv_core_ibex_primary_reg_block(kDtRvCoreIbex);
}

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
static uint32_t health_config_crc32(void) {
  uint32_t ctx;
  crc32_init(&ctx);

  // Health test thresholds, whose offsets are statically checked.
  uint32_t offset = ENTROPY_SRC_REPCNT_THRESHOLDS_REG_OFFSET;
  for (size_t i = 0; i < kNumHealthRegisters; ++i, offset += sizeof(uint32_t)) {
    crc32_add32(&ctx, abs_mmio_read32(entropy_src_base() + offset));
  }
  crc32_add32(&ctx, abs_mmio_read32(entropy_src_base() +
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
  if (kBootStage == kBootStageOwner ||
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RNG_EN_OFFSET) ==
          kHardenedBoolTrue) {
    // When bit-0 is clear an EDN request for new data for RND_DATA is
    // pending.
    while (!(abs_mmio_read32(ibex_base() + RV_CORE_IBEX_RND_STATUS_REG_OFFSET) &
             1)) {
    }
  }
  uint32_t mcycle;
  CSR_READ(CSR_REG_MCYCLE, &mcycle);
  return mcycle +
         abs_mmio_read32(ibex_base() + RV_CORE_IBEX_RND_DATA_REG_OFFSET);
}

// Provides the source of randomness for `hardened_memshred` (see
// `hardened_memory.h`). Declare as weak in case the cryptolib driver is also
// included.
OT_WEAK
uint32_t hardened_memshred_random_word(void) { return rnd_uint32(); }

// Provides the source of randomness for `random_order` (see `random_order.h`).
// Declare as weak in case the cryptolib driver is also included.
OT_WEAK
uint32_t random_order_random_word(void) { return rnd_uint32(); }
