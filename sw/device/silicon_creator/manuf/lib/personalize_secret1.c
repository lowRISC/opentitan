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

OT_WARN_UNUSED_RESULT
static status_t otp_secret_write(uint32_t offset, size_t len) {
  uint64_t data[4];
  if (len > 4) {
    return INTERNAL();
  }

  for (size_t i = 0; i < len; ++i) {
    uint32_t word0 = get_random_word();
    uint32_t word1 = get_random_word();
    data[i] = ((uint64_t)word1 << 32) | word0;
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

  TRY(otp_dai_write64_raw(OTP_CTRL_PARAM_SECRET1_OFFSET + offset, data, len));
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

  TRY(otp_dai_digest_lock_raw(OTP_CTRL_PARAM_SECRET1_OFFSET, 0));

  return OK_STATUS();
}

status_t manuf_personalize_device_secret1_check(void) {
  bool is_locked = abs_mmio_read32(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR +
                                   OTP_CTRL_SECRET1_DIGEST_0_REG_OFFSET) != 0;
  return is_locked ? OK_STATUS() : INTERNAL();
}
