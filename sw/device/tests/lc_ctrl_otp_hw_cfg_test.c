// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_otp_ctrl_t otp;
static dif_lc_ctrl_t lc;

OTTF_DEFINE_TEST_CONFIG();
static const uint8_t kNumDeviceId = 8;

/**
 * Read and return 32-bit OTP data via the DAI interface.
 */
static void otp_ctrl_dai_read_32(const dif_otp_ctrl_t *otp,
                                 dif_otp_ctrl_partition_t partition,
                                 uint32_t address, uint32_t *buf) {
  CHECK_DIF_OK(dif_otp_ctrl_dai_read_start(otp, partition, address));
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(otp));
  CHECK_DIF_OK(dif_otp_ctrl_dai_read32_end(otp, buf));
}

/**
 * Tests that the OTP sends correct HW_CFG partition data to the receiving IPs.
 */
// TODO: needs to support other recipients besides LC_CTRL.
bool test_main(void) {
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));

  mmio_region_t lc_reg = mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR);
  CHECK_DIF_OK(dif_lc_ctrl_init(lc_reg, &lc));

  dif_otp_ctrl_config_t config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x3ffff,
      .consistency_period_mask = 0x3ffffff,
  };
  CHECK_DIF_OK(dif_otp_ctrl_configure(&otp, config));

  // Read out Device ID from LC_CTRL's `device_id` registers.
  dif_lc_ctrl_device_id_t lc_device_id;
  CHECK_DIF_OK(dif_lc_ctrl_get_device_id(&lc, &lc_device_id));

  // Read out Device ID from OTP DAI read, and compare the value with LC_CTRL's
  // `device_id` registers.
  // TODO: current HW CFG value is randomly genenrated from the HJSON file,
  // plan to backdoor inject.
  uint32_t otp_device_id;
  for (uint32_t i = 0; i < kNumDeviceId; i++) {
    otp_ctrl_dai_read_32(&otp, kDifOtpCtrlPartitionHwCfg, i * 4,
                         &otp_device_id);

    CHECK(otp_device_id == lc_device_id.data[i],
          "Device_ID_%d mismatch bewtween otp_ctrl: %08x and lc_ctrl: %08x", i,
          otp_device_id, lc_device_id.data[i]);
  }
  return true;
}
