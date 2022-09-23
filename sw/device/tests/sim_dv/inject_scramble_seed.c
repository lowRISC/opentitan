// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

static dif_rstmgr_t rstmgr;
static dif_otp_ctrl_t otp_ctrl;

#define WORD_SIZE sizeof(uint64_t)

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  dif_rstmgr_reset_info_bitfield_t info;
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));

  info = rstmgr_testutils_reason_get();

  bool secret1_locked = false;
  CHECK_DIF_OK(dif_otp_ctrl_is_digest_computed(
      &otp_ctrl, kDifOtpCtrlPartitionSecret1, &secret1_locked));

  if (!secret1_locked && (info & kDifRstmgrResetInfoPor)) {
    LOG_INFO("Powered up for the first time, program and lock otp");
    // populate the scramble seeds in otp
    rand_testutils_reseed();

    // secret partition must be 64b aligned...for some reason.
    // Figure out that part later
    for (uint32_t i = 0;
         i < OTP_CTRL_PARAM_FLASH_ADDR_KEY_SEED_SIZE / WORD_SIZE; ++i) {
      uint64_t val =
          (uint64_t)rand_testutils_gen32() << 32 | rand_testutils_gen32();
      uint32_t addr = (OTP_CTRL_PARAM_FLASH_ADDR_KEY_SEED_OFFSET -
                       OTP_CTRL_PARAM_SECRET1_OFFSET) +
                      i * WORD_SIZE;
      CHECK_DIF_OK(dif_otp_ctrl_dai_program64(
          &otp_ctrl, kDifOtpCtrlPartitionSecret1, addr, val));
      otp_ctrl_testutils_wait_for_dai(&otp_ctrl);
    };

    for (uint32_t i = 0;
         i < OTP_CTRL_PARAM_FLASH_DATA_KEY_SEED_SIZE / WORD_SIZE; ++i) {
      uint64_t val =
          (uint64_t)rand_testutils_gen32() << 32 | rand_testutils_gen32();
      uint32_t addr = (OTP_CTRL_PARAM_FLASH_DATA_KEY_SEED_OFFSET -
                       OTP_CTRL_PARAM_SECRET1_OFFSET) +
                      i * WORD_SIZE;

      CHECK_DIF_OK(dif_otp_ctrl_dai_program64(
          &otp_ctrl, kDifOtpCtrlPartitionSecret1, addr, val));
      otp_ctrl_testutils_wait_for_dai(&otp_ctrl);
    };

    for (uint32_t i = 0; i < OTP_CTRL_PARAM_SRAM_DATA_KEY_SEED_SIZE / WORD_SIZE;
         ++i) {
      uint64_t val =
          (uint64_t)rand_testutils_gen32() << 32 | rand_testutils_gen32();
      uint32_t addr = (OTP_CTRL_PARAM_SRAM_DATA_KEY_SEED_OFFSET -
                       OTP_CTRL_PARAM_SECRET1_OFFSET) +
                      i * WORD_SIZE;
      CHECK_DIF_OK(dif_otp_ctrl_dai_program64(
          &otp_ctrl, kDifOtpCtrlPartitionSecret1, addr, val));
      otp_ctrl_testutils_wait_for_dai(&otp_ctrl);
    };

    // lock the secret1 partition
    CHECK_DIF_OK(
        dif_otp_ctrl_dai_digest(&otp_ctrl, kDifOtpCtrlPartitionSecret1, 0));
    otp_ctrl_testutils_wait_for_dai(&otp_ctrl);

    // inform rom to setup scramble next round
    uint32_t otp_val = 0;
    otp_val = bitfield_field32_write(
        otp_val, FLASH_CTRL_DEFAULT_REGION_SCRAMBLE_EN_FIELD,
        kMultiBitBool4True);
    CHECK_DIF_OK(dif_otp_ctrl_dai_program32(
        &otp_ctrl, kDifOtpCtrlPartitionCreatorSwCfg,
        (OTP_CTRL_PARAM_CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG_OFFSET -
         OTP_CTRL_PARAM_CREATOR_SW_CFG_OFFSET),
        otp_val));
    otp_ctrl_testutils_wait_for_dai(&otp_ctrl);

    // reset the device
    LOG_INFO("Completed first phase, reboot");
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    wait_for_interrupt();
  } else if (secret1_locked && (info & kDifRstmgrResetInfoPor)) {
    LOG_INFO("Hello World");
    return true;
  } else {
    LOG_ERROR(
        "The test should never have reached here, serect1 lock: %d, info: 0x%x",
        secret1_locked, info);
  }

  return false;
}
