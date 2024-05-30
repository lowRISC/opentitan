// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

static dif_otp_ctrl_t otp;
static dif_rstmgr_t rstmgr;

enum {
  kLastWriteValue = 0x77778888,
};

static const uint32_t kTestData[] = {
    0x11112222,
    0x33334444,
    0x55556666,
    kLastWriteValue,
};

OTTF_DEFINE_TEST_CONFIG();

typedef struct partition_data {
  dif_otp_ctrl_partition_t partition;
  size_t size;
} partition_data_t;

static const partition_data_t kPartitions[] = {
    {
        .partition = kDifOtpCtrlPartitionVendorTest,
        .size = OTP_CTRL_PARAM_VENDOR_TEST_SIZE / sizeof(uint32_t),
    },
    {
        .partition = kDifOtpCtrlPartitionCreatorSwCfg,
        .size = OTP_CTRL_PARAM_CREATOR_SW_CFG_SIZE / sizeof(uint32_t),
    },
    {
        .partition = kDifOtpCtrlPartitionOwnerSwCfg,
        .size = OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE / sizeof(uint32_t),
    },
    {
        .partition = kDifOtpCtrlPartitionRotCreatorAuthCodesign,
        .size =
            OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_SIZE / sizeof(uint32_t),
    },
    {
        .partition = kDifOtpCtrlPartitionRotCreatorAuthState,
        .size = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_STATE_SIZE / sizeof(uint32_t),
    },
};

static void peripheral_handles_init(void) {
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
}

static void otp_ctrl_dai_write_test(bool expect_eq) {
  for (uint32_t i = 0; i < ARRAYSIZE(kTestData); ++i) {
    LOG_INFO("Programming word kTestData[%d] = 0x%08x.", i, kTestData[i]);
    CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));

    uint32_t address = 0x10 + i * sizeof(uint32_t);
    CHECK_DIF_OK(
        dif_otp_ctrl_dai_program32(&otp, kDifOtpCtrlPartitionVendorTest,
                                   address, kTestData[i]),
        "Failed to program word kTestData[%d] = 0x%08x.", i, kTestData[i]);
  }
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));

  uint32_t readout[ARRAYSIZE(kTestData)] = {0};
  CHECK_STATUS_OK(otp_ctrl_testutils_dai_read32_array(
      &otp, kDifOtpCtrlPartitionVendorTest, 0x10, readout, ARRAYSIZE(readout)));

  if (expect_eq) {
    CHECK_ARRAYS_EQ(readout, kTestData, ARRAYSIZE(kTestData));
  } else {
    CHECK_ARRAYS_NE(readout, kTestData, ARRAYSIZE(kTestData));
  }
}

static void dai_disable(void) {
  CHECK_DIF_OK(dif_otp_ctrl_dai_lock(&otp));

  bool is_locked;
  CHECK_DIF_OK(dif_otp_ctrl_dai_is_locked(&otp, &is_locked));
  CHECK(is_locked);
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
}

static void otp_ctrl_dai_disable_test(uint32_t last_dai_value) {
  dai_disable();
  LOG_INFO("Checking that the DAI is disabled.");
  for (uint32_t i = 0; i < ARRAYSIZE(kPartitions); ++i) {
    const partition_data_t *partition = &kPartitions[i];
    LOG_INFO("Checking partition %d.", partition->partition);
    uint32_t readout[partition->size];
    CHECK_STATUS_OK(otp_ctrl_testutils_dai_read32_array(
        &otp, partition->partition, 0, readout, ARRAYSIZE(readout)));

    // The current DAI locking mechanism just locks the register inteface, so
    // all transactions should result in a DAI idle status.
    dif_otp_ctrl_status_t status;
    CHECK_DIF_OK(dif_otp_ctrl_get_status(&otp, &status));
    CHECK(status.codes == (1 << kDifOtpCtrlStatusCodeDaiIdle));

    // The last register value is preserved by the DAI interface. We compare
    // all read values against this to ensure that the DAI interface is not
    // returning any read values.
    for (uint32_t j = 0; j < ARRAYSIZE(readout); ++j) {
      CHECK(readout[j] == last_dai_value,
            "Partition %d, word %d: expected 0x%08x, got 0x%08x.",
            partition->partition, j, last_dai_value, readout[j]);
    }
  }
}

bool test_main(void) {
  peripheral_handles_init();

  CHECK_DIF_OK(
      dif_otp_ctrl_configure(&otp, (dif_otp_ctrl_config_t){
                                       .check_timeout = 100000,
                                       .integrity_period_mask = 0x3ffff,
                                       .consistency_period_mask = 0x3ffffff,
                                   }));

  const dif_rstmgr_reset_info_bitfield_t reset_info =
      rstmgr_testutils_reason_get();
  if (reset_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Power-on reset detected.");
    dai_disable();
    otp_ctrl_dai_write_test(/*expect_eq=*/false);

    rstmgr_testutils_reason_clear();
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));

    // Wait here until device reset.
    wait_for_interrupt();

    // Should never reach this.
    return false;
  }

  CHECK(reset_info == kDifRstmgrResetInfoSw, "Unexpected reset reason: %08x",
        reset_info);
  LOG_INFO("Software reset detected.");

  otp_ctrl_dai_write_test(/*expect_eq=*/true);
  otp_ctrl_dai_disable_test(kLastWriteValue);
  return true;
}
