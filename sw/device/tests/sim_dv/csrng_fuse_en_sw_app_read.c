// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.
#include "otp_ctrl_regs.h"                            // Generated

OTTF_DEFINE_TEST_CONFIG();

/**
 * OTP HW partition relative IFETCH offset in bytes.
 *
 * x = OTP_CTRL_PARAM_EN_SRAM_IFETCH_OFFSET (1728)
 * y = OTP_CTRL_PARAM_HW_CFG_OFFSET (1664)
 * IFETCH_OFFSET = (x - y) = 64
 */
static const uint32_t kOtpIfetchHwRelativeOffset =
    OTP_CTRL_PARAM_EN_SRAM_IFETCH_OFFSET - OTP_CTRL_PARAM_HW_CFG_OFFSET;

/**
 * OTP can only be accessed by 32b aligned addresses. As `csrng_sw_app_read` is
 * not aligned, we read from the previous aligned address and use the following
 * offset in bits to access the `csrng_sw_app_read` byte.
 */
static const uint32_t kOtpCsrngFwReadBitOffset =
    (OTP_CTRL_PARAM_EN_CSRNG_SW_APP_READ_OFFSET -
     OTP_CTRL_PARAM_EN_SRAM_IFETCH_OFFSET) *
    8;

/**
 * CTR DRBG Known-Answer-Test (KAT) for GENERATE command.
 */
static void test_fuse_enable(const dif_csrng_t *csrng) {
  csrng_testutils_fips_instantiate_kat(csrng, /*fail_expected=*/false);
  csrng_testutils_fips_generate_kat(csrng);
}

/**
 * Check that the internal states will read zero.
 */
static void test_fuse_disable(const dif_csrng_t *csrng) {
  LOG_INFO("%s", __func__);
  csrng_testutils_fips_instantiate_kat(csrng, /*fail_expected=*/true);
}

/**
 * Read the otp at `HW_CFG.OTP_CTRL_PARAM_EN_CSRNG_SW_APP_READ_OFFSET` address
 * and check whether is configured by the `uvm_test_seq` as expected.
 *
 * @param expected Define the expected value for the
 * HW_CFG.EN_ENTROPY_SRC_FW_READ flag.
 */
static void check_csrng_fuse_enabled(bool expected) {
  dif_otp_ctrl_t otp;
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));

  dif_otp_ctrl_config_t config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x3ffff,
      .consistency_period_mask = 0x3ffffff,
  };
  CHECK_DIF_OK(dif_otp_ctrl_configure(&otp, config));
  otp_ctrl_testutils_wait_for_dai(&otp);

  uint32_t value;
  // Read the current value of the partition.
  CHECK_DIF_OK(dif_otp_ctrl_dai_read_start(&otp, kDifOtpCtrlPartitionHwCfg,
                                           kOtpIfetchHwRelativeOffset));
  otp_ctrl_testutils_wait_for_dai(&otp);
  CHECK_DIF_OK(dif_otp_ctrl_dai_read32_end(&otp, &value));
  multi_bit_bool_t enable = bitfield_field32_read(
      value,
      (bitfield_field32_t){.mask = 0xff, .index = kOtpCsrngFwReadBitOffset});
  CHECK((enable == kMultiBitBool8True) == expected,
        "`fw_enable` not expected (%x)", enable);
}

/**
 * This test takes the following steps:
 *
 * - Initialize the OTP with `HW_CFG.OTP_CTRL_PARAM_EN_CSRNG_SW_APP_READ_OFFSET`
 * fuse bit set to enabled in the `uvm_test_seq`.
 * - Issue an instantiate command to request entropy.
 * - Verify that SW can read the internal states.
 * - Reset the chip and repeat the steps above, but this time, with
 *   `HW_CFG.OTP_CTRL_PARAM_EN_CSRNG_SW_APP_READ_OFFSET` fuse bit set to 0.
 * - Verify that the SW reads back all zeros when reading the internal states.
 */
bool test_main(void) {
  dif_csrng_t csrng;
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  dif_rstmgr_t rstmgr;
  dif_rstmgr_reset_info_bitfield_t info;
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  info = rstmgr_testutils_reason_get();

  if (info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Powered up for the first time");
    check_csrng_fuse_enabled(true);
    test_fuse_enable(&csrng);

    // Reboot device.
    rstmgr_testutils_reason_clear();
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    // This log message is extremely important for the test, as the
    // `uvm_test_seq` uses it to change the otp values.
    LOG_INFO("Software resetting!");
    // Wait here until device reset.
    wait_for_interrupt();
  } else if (info == kDifRstmgrResetInfoSw) {
    LOG_INFO("Powered up for the second time");

    check_csrng_fuse_enabled(false);
    test_fuse_disable(&csrng);
    return true;
  }
  return false;
}
