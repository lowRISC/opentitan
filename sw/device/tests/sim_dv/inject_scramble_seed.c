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
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

static dif_rstmgr_t rstmgr;
static dif_otp_ctrl_t otp_ctrl;

enum { kFlashWordSize = FLASH_CTRL_PARAM_BYTES_PER_WORD };

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));

  bool secret1_locked = false;
  CHECK_DIF_OK(dif_otp_ctrl_is_digest_computed(
      &otp_ctrl, kDifOtpCtrlPartitionSecret1, &secret1_locked));

  if (!secret1_locked) {
    LOG_INFO("Powered up for the first time, program and lock otp");
    // populate the scramble seeds in otp
    rand_testutils_reseed();

    // secret partition must be 64b aligned...for some reason.
    // Figure out that part later
    enum {
      kFlashAddrKeyOffset = OTP_CTRL_PARAM_FLASH_ADDR_KEY_SEED_OFFSET -
                            OTP_CTRL_PARAM_SECRET1_OFFSET,
      kFlashDataKeyOffset = OTP_CTRL_PARAM_FLASH_DATA_KEY_SEED_OFFSET -
                            OTP_CTRL_PARAM_SECRET1_OFFSET,
      kSramDataKeyOffset = OTP_CTRL_PARAM_SRAM_DATA_KEY_SEED_OFFSET -
                           OTP_CTRL_PARAM_SECRET1_OFFSET
    };

    for (uint32_t i = 0; i < OTP_CTRL_PARAM_FLASH_ADDR_KEY_SEED_SIZE;
         i += kFlashWordSize) {
      uint64_t val =
          (uint64_t)rand_testutils_gen32() << 32 | rand_testutils_gen32();

      CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp_ctrl,
                                              kDifOtpCtrlPartitionSecret1,
                                              kFlashAddrKeyOffset + i, val));
      otp_ctrl_testutils_wait_for_dai(&otp_ctrl);
    };

    for (uint32_t i = 0; i < OTP_CTRL_PARAM_FLASH_DATA_KEY_SEED_SIZE;
         i += kFlashWordSize) {
      uint64_t val =
          (uint64_t)rand_testutils_gen32() << 32 | rand_testutils_gen32();

      CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp_ctrl,
                                              kDifOtpCtrlPartitionSecret1,
                                              kFlashDataKeyOffset + i, val));
      otp_ctrl_testutils_wait_for_dai(&otp_ctrl);
    };

    for (uint32_t i = 0; i < OTP_CTRL_PARAM_SRAM_DATA_KEY_SEED_SIZE;
         i += kFlashWordSize) {
      uint64_t val =
          (uint64_t)rand_testutils_gen32() << 32 | rand_testutils_gen32();

      CHECK_DIF_OK(dif_otp_ctrl_dai_program64(
          &otp_ctrl, kDifOtpCtrlPartitionSecret1, kSramDataKeyOffset + i, val));
      otp_ctrl_testutils_wait_for_dai(&otp_ctrl);
    };

    // lock the secret1 partition
    otp_ctrl_testutils_lock_partition(&otp_ctrl, kDifOtpCtrlPartitionSecret1,
                                      0);

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

    // Check to see if there are any otp_ctrl errors
    dif_otp_ctrl_status_t status;
    CHECK_DIF_OK(dif_otp_ctrl_get_status(&otp_ctrl, &status));

    // There should not have been any errors
    // The only bit that should be asserted is the IDLE bit.
    LOG_INFO("otp_ctrl status: 0x%x", status.codes);
    CHECK(status.codes == 1 << OTP_CTRL_STATUS_DAI_IDLE_BIT);

    // reset the device
    LOG_INFO("Completed first phase, wait for reset");
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    wait_for_interrupt();
    return false;
  } else if (secret1_locked) {
    LOG_INFO("Hello World");
    return true;
  }
  return false;
}
