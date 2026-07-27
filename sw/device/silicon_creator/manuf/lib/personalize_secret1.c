// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/personalize_secret1.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "entropy_src_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "rv_core_ibex_regs.h"

static uint32_t get_random_word(void) {
  while (!(abs_mmio_read32(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR +
                           RV_CORE_IBEX_RND_STATUS_REG_OFFSET) &
           (1u << RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT))) {
    // Spin wait
  }
  return abs_mmio_read32(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR +
                         RV_CORE_IBEX_RND_DATA_REG_OFFSET);
}

/**
 * Sanity-check the quality of our on-chip hardware entropy.
 *
 * Note: We primarily rely on the hardware-level and ROM-enabled NIST SP 800-90B
 * health checkers (RCT and APT) running continuously in the background on
 * startup. The checks here are lightweight, on-chip sanity checks to verify
 * entropy quality and information density during scrambling-key generation.
 */
static status_t verify_entropy_quality(const uint32_t *words, size_t len) {
  // Check direct hardware NIST health test alert summary registers.
  uint32_t fail_counts =
      abs_mmio_read32(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR +
                      ENTROPY_SRC_ALERT_SUMMARY_FAIL_COUNTS_REG_OFFSET);
  if (fail_counts > 0) {
    return INTERNAL();  // Hardware-level TRNG health failure detected!
  }

  // Validate Hamming weight of every random word.
  for (size_t i = 0; i < len; ++i) {
    int pop = __builtin_popcount(words[i]);
    if (pop < 6 || pop > 26) {
      return INTERNAL();  // Highly biased/static entropy detected!
    }
  }
  return OK_STATUS();
}

OT_WARN_UNUSED_RESULT
static status_t otp_secret_write(uint32_t offset, size_t len) {
  uint32_t words[8];
  uint64_t data[4];
  if (len > 4) {
    return INTERNAL();
  }

  size_t num_words = len * 2;
  for (size_t i = 0; i < num_words; ++i) {
    words[i] = get_random_word();
  }

  // Perform lightweight on-chip sanity checks on our fetched entropy.
  TRY(verify_entropy_quality(words, num_words));

  for (size_t i = 0; i < len; ++i) {
    data[i] = ((uint64_t)words[2 * i + 1] << 32) | words[2 * i];
  }

  bool found_error = false;
  uint64_t prev_val = 0;
  for (size_t i = 0; i < len; ++i) {
    found_error |= data[i] == 0 || data[i] == UINT64_MAX || data[i] == prev_val;
    prev_val = data[i];
  }
  if (found_error) {
    return INTERNAL();
  }

  TRY(otp_dai_write64(OTP_CTRL_PARAM_SECRET1_OFFSET + offset, data, len));
  return OK_STATUS();
}

status_t manuf_personalize_device_secret1(void) {
  // Skip provisioning of SECRET1 OTP partition if already done.
  bool is_locked = abs_mmio_read32(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR +
                                   OTP_CTRL_SECRET1_DIGEST_0_REG_OFFSET) != 0;
  if (is_locked) {
    return OK_STATUS();
  }

  // Check that the HW_CFG0 OTP partition has been locked (and is activated).
  is_locked = abs_mmio_read32(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR +
                              OTP_CTRL_HW_CFG0_DIGEST_0_REG_OFFSET) != 0;
  if (!is_locked) {
    return INTERNAL();
  }

  // Check that the HW_CFG1 OTP partition has been locked (and is activated).
  is_locked = abs_mmio_read32(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR +
                              OTP_CTRL_HW_CFG1_DIGEST_0_REG_OFFSET) != 0;
  if (!is_locked) {
    return INTERNAL();
  }

  // Check that the CSRNG SW application interface is enabled in the HW_CFG1
  // partition, as we cannot provision SECRET1 without access to the CSRNG.
  uint32_t otp_hw_cfg1_settings =
      otp_dai_read32(kOtpPartitionHwCfg1, kHwCfgEnSramIfetchOffset);

  uint32_t csrng_sw_app_read =
      bitfield_field32_read(otp_hw_cfg1_settings, kCsrngAppRead);
  if (csrng_sw_app_read != kMultiBitBool8True) {
    return INTERNAL();
  }

  uint32_t dis_rv_dm_late_debug =
      bitfield_field32_read(otp_hw_cfg1_settings, kDisRvDmLateDebug);
  if (dis_rv_dm_late_debug != kMultiBitBool8True) {
    return INTERNAL();
  }

  TRY(otp_secret_write(kSecret1FlashAddrKeySeedOffset,
                       kSecret1FlashAddrKeySeed64BitWords));
  TRY(otp_secret_write(kSecret1FlashDataKeySeedOffset,
                       kSecret1FlashDataKeySeed64BitWords));
  TRY(otp_secret_write(kSecret1SramDataKeySeedOffset,
                       kSecret1SramDataKeySeed64Bitwords));

  TRY(otp_dai_digest_lock(OTP_CTRL_PARAM_SECRET1_OFFSET, 0));

  return OK_STATUS();
}

status_t manuf_personalize_device_secret1_check(void) {
  bool is_locked = abs_mmio_read32(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR +
                                   OTP_CTRL_SECRET1_DIGEST_0_REG_OFFSET) != 0;
  return is_locked ? OK_STATUS() : INTERNAL();
}
